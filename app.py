# ===============================
# 1. Imports
# ===============================
import streamlit as st
import nexlearn_folders
import os, json, uuid, random, re, html, time, hashlib, hmac, base64, copy, tempfile
from datetime import datetime, date, timedelta
import pypdfium2 as pdfium
import streamlit.components.v1 as components
import requests


# ===============================
# 2. File paths / folders
# ===============================
DATA_DIR = "data"
PDF_DIR = os.path.join(DATA_DIR, "pdfs")
NOTES_JSON = os.path.join(DATA_DIR, "notes.json")
STREAK_JSON = os.path.join(DATA_DIR, "streak_data.json")

os.makedirs(PDF_DIR, exist_ok=True)


# ===============================
# 3. Helper functions
# ===============================

ABBREVIATIONS = [
    "U.S.", "U.K.", "U.N.", "e.g.", "i.e.", "etc.", "vs.", "Mr.", "Mrs.", "Ms.", "Dr.",
    "Prof.", "Sr.", "Jr.", "Inc.", "Ltd.", "Co.", "St.", "Ave.", "a.m.", "p.m.", "No.",
]
_ABBREVIATION_PATTERN = re.compile("|".join(re.escape(a) for a in ABBREVIATIONS), re.IGNORECASE)

# Matches 2+ consecutive ALL-CAPS words (e.g. "WINSTON BROWN"), used to
# recase names/headings the source PDF rendered in all-caps for styling.
_ALL_CAPS_RUN_PATTERN = re.compile(r"\b[A-Z]{2,}(?:\s+[A-Z]{2,}){1,}\b")


def _title_case_caps_run(match: "re.Match") -> str:
    words = match.group(0).split()
    # Leave alone if every word is short enough to plausibly be a run of
    # acronyms (e.g. "NASA ORAS DRC") rather than a name rendered in caps.
    if all(len(w) <= 4 for w in words):
        return match.group(0)
    return " ".join(w.capitalize() for w in words)


def normalize_all_caps_names(text: str) -> str:
    """Recase multi-word ALL-CAPS runs (names/headings the source PDF
    rendered in caps for styling, e.g. "WINSTON BROWN") to Title Case, while
    leaving short all-caps acronym sequences untouched. Known abbreviations
    are protected first so e.g. "U.S." never gets caught up in this."""
    if not text:
        return text
    protected = _ABBREVIATION_PATTERN.sub(lambda m: m.group(0).replace(".", "\x01"), text)
    protected = _ALL_CAPS_RUN_PATTERN.sub(_title_case_caps_run, protected)
    return protected.replace("\x01", ".")


# A lone capital letter followed by a period and another capitalized word is
# almost always a person's initial ("D. Winston Brown", "J. K. Rowling"), not
# a sentence end. Without this, a name like that gets sliced in half - e.g.
# "...is one of D." / "Winston Brown had risen early..." - leaving a card
# built from the dangling first half.
_INITIAL_PATTERN = re.compile(r"\b[A-Z]\.(?=\s+[A-Z])")


def split_into_sentences(text: str):
    """Split text into sentences without breaking on periods inside common
    abbreviations (e.g. "U.S." or "Dr.") or a person's initial ("D. Brown"),
    which would otherwise get cut mid-name."""
    if not text:
        return []

    protected = _ABBREVIATION_PATTERN.sub(lambda m: m.group(0).replace(".", "\x01"), text)
    protected = _INITIAL_PATTERN.sub(lambda m: m.group(0)[:-1] + "\x01", protected)
    parts = re.split(r"(?<=[.!?])\s+", protected)
    return [p.replace("\x01", ".") for p in parts]


def generate_flashcards_from_text(text: str, max_cards: int = 8):
    """
    FREE/local flashcards generator (no API).
    Tries to pull: definitions, key facts, and good study Q/A pairs from the note text.

    Runs in progressively more lenient tiers (best-quality definitions first,
    then general facts, then a relaxed pass over whatever's left) so that
    short or list-heavy notes (a one-page resume, for instance) still reach
    max_cards instead of stopping at whatever the strict tiers alone find.
    """
    if not text or not text.strip():
        return []

    # normalize_quiz_sentence (not just whitespace collapse) so old notes whose
    # stored text predates a cleanup fix - e.g. the raw Private Use Area
    # "tofu box" bullet characters some PDFs use - still come out clean here,
    # without needing the note to be re-uploaded.
    cleaned = normalize_quiz_sentence(text)

    # Split into sentences (simple)
    sentences = split_into_sentences(cleaned)

    cards = []
    used_keys = set()  # simplified sentence text already spent on a card, so tiers don't repeat one another

    # PDF text extraction sometimes splits an abbreviation like "e.g." across
    # two "sentences" (e.g. "...issues (e." / "g., dynamic..."), leaving a
    # dangling fragment such as "(e." right at the end of a line. A card
    # ending mid-abbreviation like that reads as broken, so those are
    # rejected rather than shown.
    _dangling_fragment = re.compile(r"\(\s*[A-Za-z]\.\s*$")

    def _has_repeated_phrase(text: str) -> bool:
        """True if the same 3-word phrase occurs twice. PDFs sometimes glue a
        cut-off caption straight into a repeated heading or byline (e.g.
        "Writer D. Winston Brown is one of D. Winston Brown had risen
        early..."), which reads as nonsense but wasn't malformed enough for
        any other check to catch on its own."""
        words = [w.strip(".,;:!?\"'()") for w in text.lower().split()]
        words = [w for w in words if w]
        if len(words) < 8:
            return False
        seen = set()
        for i in range(len(words) - 2):
            gram = " ".join(words[i:i + 3])
            if gram in seen:
                return True
            seen.add(gram)
        return False

    # Narrative/essay-style notes (as opposed to a textbook or resume) are full
    # of short "X is Y" sentences that are really just dialogue or grammatical
    # asides, not definitions - e.g. "But this is not about guns." or
    # ""What the hell is that?" "It's a gun," Spoon said." A card built from
    # either of those is nonsense, so both are filtered out before a card is
    # ever made from them, not just cleaned up after the fact.
    _quote_chars = re.compile(r'["“”]')
    _dialogue_verb = re.compile(r"\b(said|asked|replied|shouted|whispered|exclaimed|muttered|yelled)\b", re.IGNORECASE)

    def _looks_like_dialogue(text: str) -> bool:
        return bool(_quote_chars.search(text) or _dialogue_verb.search(text))

    # A tier-1 "X is Y" match's captured "X" is everything from the start of
    # the sentence up to " is " - fine for "Python is a language", but for a
    # sentence with a fronted clause ("In paragraph 34, Brown is joining...",
    # "Notice that Brown is joining...") it captures that whole lead-in as
    # the "term" too. These are stripped off (there can be more than one
    # layered together) before the term is judged or used.
    _LEADING_DISCOURSE = re.compile(
        r"^(but|and|so|yet|however|then|now|well|rather|indeed|thus|hence|yes|no|"
        r"notice that|note that|remember that|keep in mind that|recall that)\s+",
        re.IGNORECASE,
    )
    # A glued-on heading ("Two: The hole...") or a footnote/citation marker
    # stuck to the front of a sentence ("7 'A chronology of compassion'...",
    # "12 Theidon, supra n 7...") - both common in scanned academic PDFs.
    _LEADING_LABEL = re.compile(r"^([A-Za-z0-9]{1,12}:|\d{1,3}(?=\s+[A-Z\"']))\s*")
    _LEADING_ADVERBIAL = re.compile(
        r"^(in|on|at|during|after|before|since|while|as|for|throughout|by|through)\b.{0,40}?,\s*",
        re.IGNORECASE,
    )
    _FUNCTION_WORDS = {
        "this", "that", "these", "those", "it", "its", "he", "she", "him", "her", "his", "hers",
        "they", "them", "their", "theirs", "we", "us", "our", "ours", "i", "me", "my", "mine",
        "you", "your", "yours", "there", "here", "what", "who", "which", "why", "how", "when",
        "where", "the", "a", "an", "hell", "s", "such", "yes", "no", "rather", "indeed",
    }

    def _clean_term(term: str):
        """Strips the lead-in clutter above off a tier-1 candidate term, then
        rejects it outright (returns None) if what's left is still a pronoun,
        discourse filler, or fragment (e.g. "This", "But this", "What the
        hell") rather than something genuinely definable."""
        cleaned = term
        for _ in range(3):  # a term can carry more than one of these stacked up
            before = cleaned
            cleaned = _LEADING_DISCOURSE.sub("", cleaned).strip()
            cleaned = _LEADING_LABEL.sub("", cleaned).strip()
            cleaned = _LEADING_ADVERBIAL.sub("", cleaned).strip()
            if cleaned == before:
                break
        cleaned = cleaned.rstrip(" ,;:")
        words = [w.strip(".,;:!?\"'").lower() for w in cleaned.split()]
        words = [w for w in words if w]
        if not words or words[0] in _FUNCTION_WORDS:
            return None
        # A real term (e.g. "Isolation", "the Civil Rights Act") would never
        # legitimately have a bare "I"/"we"/"you" in the middle of it - that's
        # a sign two clauses got run together, e.g. "tattoos, I know all they
        # want in life" (from ""...tattoos, I know all they want in life is
        # to be men..."), where the real subject is only the part after "I know".
        if any(w in ("i", "we", "you", "my", "our", "us", "me") for w in words[1:]):
            return None
        # Real terms have at least one substantial content word.
        if not any(w not in _FUNCTION_WORDS and len(w) > 2 for w in words):
            return None
        return cleaned

    def add_card(question: str, answer: str, require_capitalized: bool = False, check_question_overlap: bool = False):
        answer = normalize_quiz_sentence(answer)
        # `question` is already a clean template + a pre-normalized fragment
        # (see call sites below) - re-running it through normalize_quiz_sentence
        # would mangle the template's own literal "..." into ". . .".
        if not answer or not question or _dangling_fragment.search(answer):
            return False
        if _looks_like_dialogue(answer) or _looks_like_dialogue(question):
            return False
        if _has_repeated_phrase(answer):
            return False
        # Only for tier-1 "What is X?" cards, where the term and the answer
        # are supposed to be two distinct things: a repeat between them (e.g.
        # term "Writer D. Winston Brown" with an answer starting "one of D.
        # Winston Brown had risen early...") means a caption got glued to a
        # repeated heading. Tier-3's "What does the note say about X? / X"
        # cards restate X in the answer by design, so this isn't checked there.
        if check_question_overlap and _has_repeated_phrase(f"{question} {answer}"):
            return False
        # A real sentence/clause starts with a capital letter or a digit. A
        # lowercase letter, or a stray leading comma/other punctuation, almost
        # always means the extractor caught the tail end of a sentence whose
        # beginning was lost or rejected elsewhere - e.g. ", dynamic image
        # scaling..." - which reads as broken on a card. (Not applied to
        # tier-1 definitions: "X is a programming language" naturally
        # continues lowercase after "is", and that's fine.)
        if require_capitalized and not (answer[:1].isupper() or answer[:1].isdigit()):
            return False
        # Dedup by question too, not just answer: the same mis-parsed proper
        # noun (e.g. an author's name used as a sentence subject, not an
        # actual defined term) can otherwise turn into several cards that all
        # ask the identical "What is Brown?" with a different answer each time.
        answer_key = simplify_text_key(answer)
        question_key = simplify_text_key(question)
        if answer_key in used_keys or question_key in used_keys:
            return False
        used_keys.add(answer_key)
        used_keys.add(question_key)
        cards.append({"q": question, "a": answer})
        return True

    def trim_at_boundary(text: str, limit: int) -> str:
        """Shorten `text` to at most `limit` chars without cutting mid-word,
        preferring to end at a comma/semicolon if one is reasonably close."""
        if len(text) <= limit:
            return text
        window = text[:limit]
        cut = max(window.rfind(","), window.rfind(";"))
        if cut < limit * 0.4:  # too far back to be a useful cut point
            cut = window.rfind(" ")
        if cut <= 0:
            cut = limit
        return text[:cut].rstrip(" ,;:-") + "…"

    # 1) Definition-style cards (best quality)
    # Patterns like: "X is ...", "X are ...", "X means ..."
    def_patterns = [
        ("is", r"^(.{3,60}?)\s+is\s+(.{10,200})$"),
        ("are", r"^(.{3,60}?)\s+are\s+(.{10,200})$"),
        ("means", r"^(.{3,60}?)\s+means\s+(.{10,200})$"),
        ("refers to", r"^(.{3,60}?)\s+refers to\s+(.{10,200})$"),
    ]
    _bare_proper_noun = re.compile(r"^[A-Z][a-z']+$")  # e.g. "Brown" - a single capitalized word

    for s in sentences:
        s2 = normalize_quiz_sentence(s).strip("•-— ")
        if len(s2) < 20 or len(s2) > 220:
            continue

        for verb, pat in def_patterns:
            m = re.match(pat, s2, flags=re.IGNORECASE)
            if m:
                raw_term = normalize_quiz_sentence(m.group(1).strip(" :;-"))
                definition = m.group(2).strip()
                # "X is running Y" (progressive aspect: X is currently doing
                # something) gets matched by the same pattern as "X is a
                # process" (a genuine definition), but isn't one - "Brown is
                # joining a conversation" doesn't define Brown. A real nominal
                # definition almost always has an article before a noun like
                # this ("is a stepping stone"), so a definition starting with
                # a bare "-ing" word is rejected as very likely the former.
                if re.match(r"^[a-zA-Z]+ing\b", definition):
                    continue
                term = _clean_term(raw_term) if raw_term else None
                # "Means"/"refers to" are almost always genuine definitions
                # ("GDP refers to...") - except when the term is just a bare
                # name, which instead usually means a person doing something
                # ("Brown refers to other events..."), not being defined.
                if term and verb in ("means", "refers to") and _bare_proper_noun.match(term):
                    term = None
                if term and len(term.split()) <= 10:
                    if add_card(f"What is {term}?", definition, check_question_overlap=True):
                        break

        if len(cards) >= max_cards:
            return cards[:max_cards]

    # 2) Fallback: turn good sentences into Q/A (facts)
    # Example: "Culture affects how people judge others." -> Q: "What does culture affect?"
    for s in sentences:
        s2 = normalize_quiz_sentence(s).strip("•-— ")
        if len(s2) < 25 or len(s2) > 180:
            continue

        words = s2.split()
        if len(words) < 6:
            continue

        # crude heuristic: question uses first ~5 words
        topic = " ".join(words[:5]).strip(" ,")
        add_card(f"Explain: {topic} ...?", s2, require_capitalized=True)

        if len(cards) >= max_cards:
            return cards[:max_cards]

    # 3) Relaxed pass: short or list-heavy notes (e.g. a one-page resume, all
    # bullet points and skill lists) often don't have enough material that
    # fits tiers 1-2's stricter length/shape rules. This widens the net -
    # shorter fragments, longer run-on lines, and comma-separated list items
    # inside them - rather than leaving the note stuck with too few cards.
    if len(cards) < max_cards:
        for s in sentences:
            s2 = normalize_quiz_sentence(s).strip("•-— ")
            if len(s2) < 12:
                continue

            words = s2.split()
            if len(words) < 4:
                continue

            topic = " ".join(words[:5]).strip(" ,:;")
            if add_card(f"Explain: {topic} ...?", trim_at_boundary(s2, 260), require_capitalized=True):
                if len(cards) >= max_cards:
                    return cards[:max_cards]

            # A long "Label: item1, item2, item3" line (common in skills/tools
            # lists) also yields one good card per sizeable item.
            for clause in re.split(r"[,;]", s2):
                clause = clause.split(":")[-1].strip(" -–—")
                if 12 <= len(clause) <= 100 and len(clause.split()) >= 2:
                    add_card(f"What does the note say about {clause}?", clause, require_capitalized=True)
                    if len(cards) >= max_cards:
                        return cards[:max_cards]

    return cards[:max_cards]


def normalize_quiz_sentence(text: str) -> str:
    """Normalize common PDF extraction artifacts for cleaner quiz text."""
    if not text:
        return ""

    # PDFs that use a symbol font (e.g. Wingdings) for bullet points often
    # extract as that font's raw Private Use Area codepoints (like \uf0b7),
    # which have no defined glyph in any other font - most viewers render
    # them as a "tofu" box. There's no legitimate use of this whole range in
    # real text, so it's dropped outright rather than matched case by case.
    normalized = re.sub(r"[\ue000-\uf8ff]+", " ", text)
    normalized = normalized.replace("\u00ad", "")  # soft hyphen
    normalized = normalized.replace("\ufeff", "")
    normalized = normalized.replace("\u2019", "'")
    normalized = normalized.replace("\u2018", "'")
    normalized = normalized.replace("\u201c", '"')
    normalized = normalized.replace("\u201d", '"')
    normalized = normalized.replace("\u2013", "-")
    normalized = normalized.replace("\u2014", "-")
    normalized = normalized.replace("\u2022", " ")
    normalized = normalized.replace("Â", "")
    normalized = normalized.replace("Ã", "")
    normalized = re.sub(r"ﬁ\s+(?=[a-z])", "fi", normalized)  # "ﬁ lled" -> "filled"
    normalized = re.sub(r"ﬂ\s+(?=[a-z])", "fl", normalized)  # "ﬂ oor" -> "floor"
    normalized = normalized.replace("ﬁ", "fi")
    normalized = normalized.replace("ﬂ", "fl")
    normalized = normalized.replace("’", "'")
    normalized = re.sub(r"(\w)-\s+(\w)", r"\1\2", normalized)  # partic- ular -> particular
    normalized = re.sub(r"([A-Z]{2,})([a-z])", r"\1 \2", normalized)  # UKgovernment -> UK government
    normalized = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", normalized)  # theUK -> the UK
    normalized = re.sub(r"(['’]s)(?=[A-Za-z])", r"\1 ", normalized)  # government'sskill -> government's skill
    normalized = re.sub(r"[_~`|¦]+", " ", normalized)
    normalized = re.sub(r"[A-Za-z']{16,}", lambda m: split_glued_token(m.group(0)), normalized)
    # Protect abbreviation periods (e.g. "U.S.") before inserting spaces after
    # punctuation, otherwise "U.s." becomes "U. s." and later gets misread as
    # two separate sentences.
    normalized = _ABBREVIATION_PATTERN.sub(lambda m: m.group(0).replace(".", "\x01"), normalized)
    # Not inserted before more punctuation (","? ".") - otherwise a real
    # ellipsis like "...?" gets pulled apart into ". . . ?".
    normalized = re.sub(r"(?<=[,;:.!?])(?=[^\s,;:.!?])", " ", normalized)
    normalized = normalized.replace("\x01", ".")
    normalized = re.sub(r"\s+", " ", normalized).strip()
    normalized = normalize_all_caps_names(normalized)
    return normalized


NOISE_KEYWORDS = {
    "chapter", "learning", "lesson", "unit", "section", "page", "copyright", "isbn", "glossary",
    "vocabulary", "figure", "table", "photo", "illustration", "review", "objectives", "summary",
    "standards", "benchmark", "teacher", "student", "worksheet", "activity", "sidebar", "abstract",
    "journal", "volume", "publication", "author", "keywords"
}


COMMON_VERBS = {
    "is", "are", "was", "were", "be", "being", "been", "have", "has", "had", "do", "does", "did",
    "can", "could", "may", "might", "will", "would", "should", "suggests", "shows", "explains",
    "describes", "argues", "causes", "creates", "helps", "means", "becomes", "includes", "affects",
    "leads", "changes", "supports", "reveals"
}


SECTION_LABELS = {
    "about the author", "abstract", "acknowledgements", "bibliography", "contents", "copyright",
    "discussion", "glossary", "index", "keywords", "learning objectives", "notes", "references",
    "review", "sidebar", "summary", "table of contents", "works cited"
}


OCR_ARTIFACT_PATTERNS = [
    r"â€¦", r"â€", r"ï¬", r"�", r"\b(?:cid|obj|endobj)\b"
]


def simplify_text_key(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", " ", text.lower()).strip()


def has_extraction_artifacts(text: str) -> bool:
    if not text:
        return False

    if any(re.search(pattern, text, flags=re.IGNORECASE) for pattern in OCR_ARTIFACT_PATTERNS):
        return True

    odd_chars = sum(1 for ch in text if not (ch.isalnum() or ch.isspace() or ch in ".,;:!?()[]{}'\"-/%&"))
    return odd_chars / max(len(text), 1) > 0.12


def sentence_case(text: str) -> str:
    text = normalize_quiz_sentence(text).strip(" ,;:-")
    if not text:
        return ""
    return text[0].upper() + text[1:]


def looks_like_noise_line(line: str, repeated_keys=None) -> bool:
    """Filter headers, footers, chapter labels, page markers, and other PDF noise."""
    if not line:
        return True

    repeated_keys = repeated_keys or set()
    compact = normalize_quiz_sentence(line)
    if not compact:
        return True

    key = simplify_text_key(compact)
    words = compact.split()
    lower_words = [w.strip(".,;:!?()[]{}\"'").lower() for w in words]

    if key in repeated_keys:
        return True

    if re.fullmatch(r"(page\s*)?\d+(\s*of\s*\d+)?", compact.lower()):
        return True

    if re.fullmatch(r"[ivxlcdm]+", compact.lower()):
        return True

    if re.fullmatch(r"chapter\s+\d+[a-z]?", compact.lower()):
        return True

    if key in SECTION_LABELS:
        return True

    if has_extraction_artifacts(compact):
        return True

    if "@" in compact or "doi" in compact.lower():
        return True

    if re.search(r"\b(vol\.?|volume|issue|journal|press|university|permissions?|email)\b", compact, flags=re.IGNORECASE):
        return True

    if re.search(r"^\d+\s*[.)]\s*$", compact):
        return True

    if re.search(r"\b(reference|references|notes|footnote|citation|cited|appendix)\b", compact, flags=re.IGNORECASE):
        return True

    if any(token in {"www", "http", "https"} for token in lower_words):
        return True

    if any(keyword in compact.lower() for keyword in ["all rights reserved", "printed in", "published by"]):
        return True

    if len(words) <= 8:
        keyword_hits = sum(1 for w in lower_words if w in NOISE_KEYWORDS)
        upper_ratio = sum(1 for ch in compact if ch.isupper()) / max(sum(1 for ch in compact if ch.isalpha()), 1)
        title_like = sum(1 for w in words if w[:1].isupper()) / max(len(words), 1)
        if keyword_hits >= 1:
            return True
        if upper_ratio > 0.72:
            return True
        if title_like > 0.85 and not re.search(r"[.!?]$", compact):
            return True
        if len(words) <= 3 and not re.search(r"[.!?]$", compact):
            return True

    digit_ratio = sum(1 for ch in compact if ch.isdigit()) / max(len(compact), 1)
    if digit_ratio > 0.2:
        return True

    if len(words) <= 12 and not re.search(r"[.!?]$", compact) and not has_meaningful_verb(compact):
        title_like = sum(1 for w in words if w[:1].isupper()) / max(len(words), 1)
        if title_like > 0.65:
            return True

    return False


def merge_extracted_lines(text: str):
    """Repair hard line breaks and hyphenation before paragraph filtering."""
    if not text:
        return []

    normalized = text.replace("\r\n", "\n").replace("\r", "\n")
    normalized = re.sub(r"(?<=\w)-\n(?=\w)", "", normalized)

    merged_lines = []
    for raw_line in normalized.split("\n"):
        current = normalize_quiz_sentence(raw_line.strip())
        if not current:
            merged_lines.append("")
            continue

        if not merged_lines or merged_lines[-1] == "":
            merged_lines.append(current)
            continue

        prev = merged_lines[-1]
        should_join = (
            not re.search(r"[.!?\"']$", prev)
            and not re.match(r"^[A-Z][A-Z\s.:-]{2,}$", prev)
            and not re.match(r"^[A-Z][A-Z\s.:-]{2,}$", current)
            and not has_extraction_artifacts(prev)
            and not has_extraction_artifacts(current)
        )

        if should_join:
            merged_lines[-1] = normalize_quiz_sentence(f"{prev} {current}")
        else:
            merged_lines.append(current)

    while merged_lines and merged_lines[-1] == "":
        merged_lines.pop()

    return merged_lines


def clean_extracted_text(text: str) -> str:
    """Keep article-style body text and remove common textbook/PDF noise."""
    if not text or not text.strip():
        return ""

    normalized_lines = merge_extracted_lines(text)

    line_counts = {}
    for line in normalized_lines:
        key = simplify_text_key(line)
        if not key:
            continue
        line_counts[key] = line_counts.get(key, 0) + 1

    repeated_keys = {
        key for key, count in line_counts.items()
        if count >= 2 and 1 <= len(key.split()) <= 10
    }

    paragraphs = []
    current = []

    for normalized_line in normalized_lines:
        if not normalized_line.strip():
            if current:
                paragraphs.append(" ".join(current))
                current = []
            continue

        if looks_like_noise_line(normalized_line, repeated_keys):
            if current:
                paragraphs.append(" ".join(current))
                current = []
            continue

        current.append(normalized_line)

    if current:
        paragraphs.append(" ".join(current))

    cleaned_paragraphs = []
    for paragraph in paragraphs:
        paragraph = normalize_quiz_sentence(paragraph)
        paragraph = re.sub(r"\b\d+\s+(?=[A-Z][a-z])", "", paragraph)
        paragraph = re.sub(r"\s*\[[^\]]{1,40}\]\s*", " ", paragraph)
        paragraph = re.sub(r"\s+", " ", paragraph).strip()
        if len(paragraph.split()) >= 8 and not looks_like_noise_line(paragraph):
            cleaned_paragraphs.append(paragraph)

    return "\n\n".join(cleaned_paragraphs)


GLUED_WORD_HINTS = {
    "a", "an", "and", "are", "as", "at", "be", "been", "by", "can", "did", "for", "from", "had", "has",
    "have", "in", "into", "is", "it", "its", "of", "on", "or", "that", "the", "their", "there", "these",
    "they", "this", "to", "was", "were", "what", "when", "which", "with", "would", "about", "between",
    "according", "census", "produced", "government", "skillset", "skills", "training", "body", "gender",
    "work", "segregation", "roles", "social", "review"
}


def split_glued_token(token: str) -> str:
    """Best-effort split for very long glued lowercase tokens."""
    core = token.strip(".,;:!?()[]{}\"")
    if len(core) < 16 or not re.fullmatch(r"[A-Za-z']+", core):
        return token

    lower = core.lower().replace("'", "")
    if len(lower) < 16:
        return token

    parts = []
    i = 0
    hints = sorted(GLUED_WORD_HINTS, key=len, reverse=True)
    n = len(lower)

    while i < n:
        match = next((w for w in hints if lower.startswith(w, i)), None)
        if match:
            parts.append(match)
            i += len(match)
            continue

        j = i + 1
        while j < n and not any(lower.startswith(w, j) for w in hints):
            j += 1
        parts.append(lower[i:j])
        i = j

    unknown_chunks = [p for p in parts if p not in GLUED_WORD_HINTS and len(p) > 2]
    if len(parts) < 2 or len(unknown_chunks) > 1:
        return token

    rebuilt = " ".join(parts)
    if core[0].isupper():
        rebuilt = rebuilt.capitalize()

    return token.replace(core, rebuilt, 1)


def is_readable_quiz_sentence(text: str) -> bool:
    """Reject sentences that still look heavily merged/garbled after cleanup."""
    if not text:
        return False

    words = text.split()
    if len(words) < 8:
        return False

    if any(len(w.strip(".,;:!?\"'()[]{}")) > 22 for w in words):
        return False

    space_ratio = text.count(" ") / max(len(text), 1)
    if space_ratio < 0.09:
        return False

    if has_extraction_artifacts(text):
        return False

    if sum(1 for ch in text if ch.isdigit()) / max(len(text), 1) > 0.08:
        return False

    return True


def is_fragment_like_text(text: str) -> bool:
    normalized = clean_sentence_fragment(text)
    if not normalized:
        return True

    words = normalized.split()
    if len(words) < 6:
        return True

    if re.match(r"^\d+", normalized):
        return True

    if re.search(r"\b(doi|vol\.?|volume|issue|journal|press|copyright|permission|email)\b", normalized, flags=re.IGNORECASE):
        return True

    if normalized.count(":") > 1:
        return True

    alpha_words = [w for w in words if re.search(r"[A-Za-z]", w)]
    if len(alpha_words) / max(len(words), 1) < 0.75:
        return True

    return False


def is_good_quiz_source_sentence(text: str) -> bool:
    """Accept body sentences with enough meaning for a comprehension question."""
    sentence = normalize_quiz_sentence(text)
    if not sentence:
        return False

    if not (45 <= len(sentence) <= 280):
        return False

    first_alpha = next((ch for ch in sentence if ch.isalpha()), "")
    if first_alpha and not first_alpha.isupper():
        return False

    if not is_readable_quiz_sentence(sentence):
        return False

    if is_fragment_like_text(sentence):
        return False

    if "?" in sentence:
        return False

    if looks_like_noise_line(sentence):
        return False

    words = [w.strip(".,;:!?\"'()[]{}").lower() for w in sentence.split()]
    if len(words) < 9:
        return False

    if words[0] in QUESTION_STARTERS:
        return False

    verb_hits = sum(1 for w in words if w in COMMON_VERBS or w.endswith("ed") or w.endswith("ing"))
    if verb_hits < 1:
        return False

    keyword_hits = sum(1 for w in words if w in NOISE_KEYWORDS)
    if keyword_hits >= 2:
        return False

    if re.search(r"\b(chapter|lesson|unit|page|glossary|vocabulary)\b", sentence, flags=re.IGNORECASE):
        return False

    if re.search(r"\b(doi|abstract|journal|vol\.?|volume|publication|access|copyright)\b", sentence, flags=re.IGNORECASE):
        return False

    if re.search(r"\b(i|we|our|us|my|you|your)\b", sentence, flags=re.IGNORECASE):
        return False

    if re.search(r"(^|[\s(])\d{1,2}($|[\s).,])", sentence):
        return False

    if sentence.count(",") > 3 or "(" in sentence or ")" in sentence:
        return False

    return True


QUIZ_STOPWORDS = {
    "the", "and", "for", "that", "this", "with", "from", "into", "about", "between",
    "have", "has", "had", "were", "was", "are", "is", "will", "would", "could", "should",
    "their", "there", "which", "when", "what", "where", "whose", "while", "also", "than"
}


QUIZ_FILLER_WORDS = {
    "overall", "basically", "simply", "clearly", "generally", "usually", "often", "really",
    "very", "just", "kind", "sort"
}


QUESTION_STARTERS = {"who", "what", "when", "where", "why", "how"}


OPTION_BAD_ENDINGS = {
    "a", "an", "and", "as", "at", "because", "by", "for", "from", "in", "into", "of", "on",
    "or", "so", "that", "the", "their", "there", "this", "to", "with", "while"
}


SUBORDINATE_STARTERS = {
    "although", "because", "before", "despite", "if", "since", "though", "unless", "until", "when", "while"
}


BAD_OPTION_STARTS = {
    "and", "because", "by", "for", "from", "if", "or", "provides", "shows", "describes",
    "explains", "suggests", "reveals", "includes", "with", "while", "whose"
}


COMPREHENSION_MARKERS = {
    "because", "therefore", "however", "although", "but", "while", "in contrast", "as a result",
    "suggests", "implies", "shows", "reveals", "emphasizes", "highlights", "supports", "means",
    "can help", "leads to", "resulted in", "rather than"
}


def tokenize_for_similarity(text: str):
    return {
        w.lower().strip(".,;:!?\"'()[]{}")
        for w in text.split()
        if len(w.strip(".,;:!?\"'()[]{}")) > 2
    }


def jaccard_similarity(a: str, b: str) -> float:
    sa = tokenize_for_similarity(a)
    sb = tokenize_for_similarity(b)
    if not sa or not sb:
        return 0.0
    return len(sa & sb) / max(len(sa | sb), 1)


def clean_sentence_fragment(text: str) -> str:
    cleaned = normalize_quiz_sentence(text)
    cleaned = re.sub(r"\([^)]*\)", "", cleaned)
    cleaned = re.sub(r"https?://\S+", "", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"\bdoi[:\s]*\S+", "", cleaned, flags=re.IGNORECASE)
    cleaned = re.sub(r"\(\s*\d{4}\s*\)", "", cleaned)
    cleaned = re.sub(r"\[\d+\]", "", cleaned)
    cleaned = re.sub(r"\b\d{1,2}\b(?=\s+[A-Z][a-z])", "", cleaned)
    cleaned = re.sub(r"\s+", " ", cleaned).strip(" ,;:-")
    return cleaned


def trim_to_complete_phrase(text: str, max_words: int = 16) -> str:
    words = text.split()
    if len(words) <= max_words:
        return text

    boundary = None
    for idx in range(max_words - 1, -1, -1):
        token = words[idx].rstrip("\"')]}").strip()
        if token.endswith((",", ";", ":", ".", "!", "?")):
            boundary = idx + 1
            break

    if boundary and boundary >= 6:
        trimmed = words[:boundary]
    else:
        return ""

    while trimmed and trimmed[-1].strip(".,;:!?\"'()[]{}").lower() in OPTION_BAD_ENDINGS:
        trimmed.pop()
    return " ".join(trimmed).strip(" ,;:-")


def strip_leading_subordinate_clause(text: str) -> str:
    words = text.split()
    if not words:
        return ""

    first = words[0].lower().strip(".,;:!?\"'()[]{}")
    if first not in SUBORDINATE_STARTERS:
        return text

    if "," in text:
        tail = text.split(",", 1)[1].strip()
        if tail:
            return tail

    return text


def has_meaningful_verb(text: str) -> bool:
    words = [w.strip(".,;:!?\"'()[]{}").lower() for w in text.split()]
    return any(
        w in COMMON_VERBS or w.endswith("ed") or w.endswith("ing")
        for w in words
    )


def polish_option_text(sentence: str, max_words: int = 20) -> str:
    """Rewrite extracted text into a concise, readable option sentence."""
    s = clean_sentence_fragment(sentence)
    if not s:
        return ""

    clauses = [c.strip(" ,;:-") for c in re.split(r"[;:]", s) if c.strip()]
    core = clauses[0] if clauses else s
    core = strip_leading_subordinate_clause(core)
    core = re.sub(
        r"^(however|therefore|instead|for example|for instance|in addition|on the other hand)\s*,?\s*",
        "",
        core,
        flags=re.IGNORECASE,
    )

    if "," in core:
        parts = [part.strip() for part in core.split(",") if part.strip()]

        def starts_with_bad_word(part: str) -> bool:
            words = part.split()
            if not words:
                return False
            first = words[0].strip(".,;:!?\"'()[]{}").lower()
            return first in SUBORDINATE_STARTERS or first in BAD_OPTION_STARTS

        usable_parts = [part for part in parts if not starts_with_bad_word(part)]
        core = max(usable_parts or parts, key=lambda item: len(item.split()))

    core = re.sub(r"^It\b", "The passage", core)
    core = re.sub(r"^They\b", "The passage", core)
    core = re.sub(r"^(This|These)\b", "The passage", core)
    core = trim_to_complete_phrase(core, max_words=max_words)
    core = sentence_case(core).rstrip(".")
    if not core or not has_meaningful_verb(core) or is_fragment_like_text(core):
        return ""

    return f"{core}."


def summarize_sentence_for_option(sentence: str, max_words: int = 20, as_choice: bool = True) -> str:
    polished = polish_option_text(sentence, max_words=max_words)
    if not polished:
        return ""
    return polished


def extract_focus_term(sentence: str) -> str:
    words = [w.strip(".,;:!?\"'()[]{}") for w in normalize_quiz_sentence(sentence).split()]
    for w in words[:10]:
        lw = w.lower()
        if len(w) >= 4 and lw not in QUIZ_STOPWORDS and not lw.isdigit():
            return w
    return words[0] if words else "concept"


def extract_focus_phrase(sentence: str, max_words: int = 3) -> str:
    words = [w.strip(".,;:!?\"'()[]{}") for w in normalize_quiz_sentence(sentence).split()]
    phrase = []
    for w in words[:12]:
        lw = w.lower()
        if len(w) >= 3 and lw not in QUIZ_STOPWORDS and not lw.isdigit():
            phrase.append(w)
            if len(phrase) >= max_words:
                break
    if phrase:
        return " ".join(phrase)
    return extract_focus_term(sentence)


def clean_topic_phrase(topic: str) -> str:
    topic = clean_sentence_fragment(topic)
    words = [w.strip(".,;:!?\"'()[]{}") for w in topic.split()]
    picked = []
    for word in words:
        lw = word.lower()
        if len(word) >= 3 and lw not in QUIZ_STOPWORDS and lw not in QUIZ_FILLER_WORDS and not lw.isdigit():
            picked.append(word)
        if len(picked) >= 3:
            break

    if not picked:
        return "this idea"
    return " ".join(picked)


def build_question_text(sentence: str, idx: int) -> str:
    sentence_lower = sentence.lower()

    if any(marker in sentence_lower for marker in ["because", "as a result", "therefore", "leads to", "resulted in"]):
        return "According to the passage, which outcome is described?"
    if any(marker in sentence_lower for marker in ["however", "although", "but", "while", "in contrast"]):
        return "Which statement best captures the contrast in the passage?"
    if any(marker in sentence_lower for marker in ["should", "must", "need to", "can help"]):
        return "Based on the passage, which idea is supported?"

    templates = [
        "Which conclusion is best supported by the passage?",
        "What broader point does the passage emphasize?",
        "Which inference best follows from the passage?",
        "Which idea best reflects the passage's main point?"
    ]
    return templates[idx % len(templates)]


def comprehension_priority_score(sentence: str) -> float:
    sentence_lower = sentence.lower()
    marker_hits = sum(1 for marker in COMPREHENSION_MARKERS if marker in sentence_lower)
    complexity_bonus = 1.0 if any(marker in sentence_lower for marker in ["because", "however", "although", "therefore", "while"]) else 0.0
    return marker_hits + complexity_bonus + min(len(sentence.split()) / 20.0, 1.5)


def build_base_explanation(sentence: str) -> str:
    snippet = summarize_sentence_for_option(sentence, max_words=18, as_choice=False).rstrip(".")
    if not snippet:
        return ""
    snippet_body = snippet[0].lower() + snippet[1:]
    if snippet_body.startswith("the passage "):
        snippet_body = snippet_body[len("the passage "):]
    return f"The passage supports this answer because it states that {snippet_body}."


def build_evidence_text(sentence: str) -> str:
    evidence = sentence_case(clean_sentence_fragment(sentence))
    if not evidence:
        return "The passage directly supports this choice."
    return evidence.rstrip(".") + "."


def is_valid_question_text(text: str) -> bool:
    normalized = clean_sentence_fragment(text)
    if not normalized or not normalized.endswith("?"):
        return False
    if len(normalized.split()) < 7 or len(normalized.split()) > 22:
        return False
    if normalized[0].islower():
        return False
    if normalized.count("?") != 1:
        return False
    if re.search(r"\b(page|chapter|lesson|unit|figure|table)\b", normalized, flags=re.IGNORECASE):
        return False
    return True


def is_valid_option_text(text: str) -> bool:
    normalized = clean_sentence_fragment(text).rstrip(".")
    if not normalized:
        return False
    if "?" in normalized:
        return False
    words = normalized.split()
    if len(words) < 4 or len(words) > 24:
        return False
    if normalized[0].islower():
        return False
    if normalized.startswith(("'", '"')) or normalized.endswith(("-", ":", ";", ",")):
        return False
    first_word = words[0].strip(".,;:!?\"'()[]{}").lower()
    if first_word in BAD_OPTION_STARTS:
        return False
    if first_word.endswith("ing"):
        return False
    if first_word in COMMON_VERBS and first_word not in {"is", "are"}:
        return False
    if first_word in {"are", "can", "could", "did", "do", "does", "had", "has", "have", "is", "should", "was", "were", "would"}:
        return False
    if any(len(word.strip(".,;:!?\"'()[]{}")) > 18 for word in words):
        return False
    if words[-1].strip(".,;:!?\"'()[]{}").lower() in OPTION_BAD_ENDINGS:
        return False
    if is_fragment_like_text(normalized):
        return False
    if not has_meaningful_verb(normalized):
        return False
    return True


def options_have_consistent_style(options: list[str]) -> bool:
    if len(options) != 4:
        return False

    word_counts = [len(clean_sentence_fragment(option).rstrip(".").split()) for option in options]
    if min(word_counts) < 4:
        return False
    if max(word_counts) - min(word_counts) > 8:
        return False

    openers = [clean_sentence_fragment(option).split()[0].lower() for option in options if clean_sentence_fragment(option)]
    if any(opener.endswith("ing") for opener in openers):
        return False

    passage_openers = sum(1 for option in options if clean_sentence_fragment(option).startswith("The passage "))
    if passage_openers not in {0, len(options)}:
        return False

    return True


def distractors_are_plausible(correct_answer: str, distractors: list[str], evidence: str) -> bool:
    evidence_tokens = tokenize_for_similarity(evidence)
    correct_similarity = jaccard_similarity(correct_answer, evidence)
    if correct_similarity < 0.18:
        return False

    for distractor in distractors:
        distractor_similarity = jaccard_similarity(distractor, evidence)
        shared_tokens = len(tokenize_for_similarity(distractor) & evidence_tokens)
        if distractor_similarity >= correct_similarity - 0.05:
            return False
        if distractor_similarity > 0.58:
            return False
        if shared_tokens < 1:
            return False

    return True


def single_best_answer_is_clear(correct_answer: str, distractors: list[str], evidence: str) -> bool:
    correct_similarity = jaccard_similarity(correct_answer, evidence)
    distractor_scores = [jaccard_similarity(distractor, evidence) for distractor in distractors]
    if not distractor_scores:
        return False
    return correct_similarity >= max(distractor_scores) + 0.08


def choices_are_distinct(options) -> bool:
    option_values = list(options)
    for i in range(len(option_values)):
        for j in range(i + 1, len(option_values)):
            if jaccard_similarity(option_values[i], option_values[j]) > 0.74:
                return False
    return True


def is_valid_explanation_text(text: str) -> bool:
    normalized = clean_sentence_fragment(text)
    sentences = [s.strip() for s in split_into_sentences(normalized) if s.strip()]
    if not normalized or len(sentences) > 4 or len(normalized.split()) > 55:
        return False
    if "passage" not in normalized.lower():
        return False
    return True


def explanation_is_grounded(explanation: str, evidence: str) -> bool:
    if not explanation or not evidence:
        return False
    if "passage" not in explanation.lower():
        return False
    return jaccard_similarity(explanation, evidence) >= 0.12


def is_vague_explanation(explanation: str) -> bool:
    normalized = clean_sentence_fragment(explanation).lower()
    if not normalized:
        return True

    vague_patterns = [
        "main idea", "best matches", "most accurate", "best reflects", "clearly correct",
        "supported by the passage" if normalized == "supported by the passage" else ""
    ]
    if any(pattern and pattern in normalized for pattern in vague_patterns) and jaccard_similarity(normalized, normalized) >= 0:
        evidence_like = re.search(r"\b(states?|shows?|describes?|explains?)\b", normalized)
        if not evidence_like:
            return True

    return False


def correct_answer_is_pasted_fragment(correct_answer: str, evidence: str) -> bool:
    normalized_answer = clean_sentence_fragment(correct_answer).rstrip(".")
    normalized_evidence = clean_sentence_fragment(evidence).rstrip(".")
    if not normalized_answer or not normalized_evidence:
        return True

    if is_fragment_like_text(normalized_answer):
        return True

    if normalized_evidence.endswith(normalized_answer) and len(normalized_answer.split()) <= max(len(normalized_evidence.split()) - 4, 8):
        return True

    return False


def question_is_answerable_from_passage(question_text: str, correct_answer: str, evidence: str) -> bool:
    if not is_valid_question_text(question_text):
        return False
    if not evidence:
        return False

    question_tokens = tokenize_for_similarity(question_text)
    support_tokens = tokenize_for_similarity(correct_answer) | tokenize_for_similarity(evidence)
    return len(question_tokens & support_tokens) >= 1 or any(
        phrase in question_text.lower() for phrase in [
            "according to the passage", "based on the passage", "best supported by the passage",
            "passage emphasize", "passage supports"
        ]
    )


def question_targets_comprehension(question_text: str) -> bool:
    lower = question_text.lower()
    return any(
        phrase in lower for phrase in [
            "outcome", "contrast", "supported", "broader point", "inference",
            "main point", "emphasize", "conclusion"
        ]
    )


def is_fragment_matching_item(question_text: str, correct_answer: str, evidence: str) -> bool:
    normalized_answer = clean_sentence_fragment(correct_answer).rstrip(".")
    normalized_evidence = clean_sentence_fragment(evidence).rstrip(".")
    if not normalized_answer or not normalized_evidence:
        return True

    answer_overlap = jaccard_similarity(normalized_answer, normalized_evidence)
    answer_is_literal_slice = (
        normalized_answer in normalized_evidence
        or normalized_evidence.endswith(normalized_answer)
        or normalized_evidence.startswith(normalized_answer)
    )

    if answer_overlap >= 0.72 and answer_is_literal_slice and not question_targets_comprehension(question_text):
        return True

    return False


def validate_quiz_item(question_data: dict) -> bool:
    question_text = question_data.get("question", "")
    choices = question_data.get("choices", {})
    correct_option = question_data.get("correctAnswer")
    explanation = question_data.get("explanation", "")
    evidence = question_data.get("evidence", "")

    if not is_valid_question_text(question_text):
        return False
    if not isinstance(choices, dict) or set(choices.keys()) != {"A", "B", "C", "D"}:
        return False
    if correct_option not in choices:
        return False

    option_values = [choices[key] for key in ["A", "B", "C", "D"]]
    if any(not is_valid_option_text(option) for option in option_values):
        return False
    if not options_have_consistent_style(option_values):
        return False
    if not choices_are_distinct(option_values):
        return False

    correct_answer = choices[correct_option]
    distractors = [choices[key] for key in ["A", "B", "C", "D"] if key != correct_option]
    if not question_is_answerable_from_passage(question_text, correct_answer, evidence):
        return False
    if is_fragment_matching_item(question_text, correct_answer, evidence):
        return False
    if correct_answer_is_pasted_fragment(correct_answer, evidence):
        return False
    if not distractors_are_plausible(correct_answer, distractors, evidence):
        return False
    if not single_best_answer_is_clear(correct_answer, distractors, evidence):
        return False

    if not is_valid_explanation_text(explanation):
        return False
    if is_vague_explanation(explanation):
        return False
    if not explanation_is_grounded(explanation, evidence):
        return False

    return True


def build_quiz_question(sentence: str, distractor_pool: list, idx: int, max_attempts: int = 6):
    correct_answer = polish_option_text(sentence, max_words=20)
    if not is_valid_option_text(correct_answer):
        return None

    evidence = build_evidence_text(sentence)
    candidate_distractors = []
    for other in distractor_pool:
        if other == sentence:
            continue
        option = polish_option_text(other, max_words=20)
        if not is_valid_option_text(option):
            continue
        if option == correct_answer:
            continue
        if jaccard_similarity(option, correct_answer) > 0.68:
            continue
        if any(jaccard_similarity(option, existing) > 0.68 for existing in candidate_distractors):
            continue
        candidate_distractors.append(option)

    if len(candidate_distractors) < 3:
        return None

    explanation = build_base_explanation(sentence)
    if not is_valid_explanation_text(explanation):
        return None
    if not explanation_is_grounded(explanation, evidence):
        return None

    for attempt in range(max_attempts):
        shuffled_distractors = candidate_distractors[:]
        random.shuffle(shuffled_distractors)
        distractors = shuffled_distractors[:3]
        if len(distractors) < 3:
            continue

        question_text = build_question_text(sentence, idx + attempt)
        if not is_valid_question_text(question_text):
            continue

        all_options = [correct_answer] + distractors
        if not choices_are_distinct(all_options):
            continue
        if not options_have_consistent_style(all_options):
            continue
        if not distractors_are_plausible(correct_answer, distractors, evidence):
            continue
        if not single_best_answer_is_clear(correct_answer, distractors, evidence):
            continue

        shuffled_options = all_options[:]
        random.shuffle(shuffled_options)
        correct_option = chr(65 + shuffled_options.index(correct_answer))
        question_data = {
            "type": "multiple_choice",
            "question": question_text,
            "choices": {
                "A": shuffled_options[0],
                "B": shuffled_options[1],
                "C": shuffled_options[2],
                "D": shuffled_options[3]
            },
            "correctAnswer": correct_option,
            "explanation": explanation,
            "evidence": evidence
        }
        if validate_quiz_item(question_data):
            return question_data

    return None


def build_feedback_explanation(question_data: dict, selected_option: str = None) -> str:
    base = normalize_quiz_sentence(question_data.get("explanation", "")).strip()
    evidence = normalize_quiz_sentence(question_data.get("evidence", "") or question_data.get("source_sentence", "")).strip()
    correct_option = question_data.get("correctAnswer") or question_data.get("correct_answer")
    correct_text = normalize_quiz_sentence(question_data.get("choices", {}).get(correct_option, ""))

    # The "your answer focuses on X instead of Y" comparison below only makes
    # sense when both options are substantial written-out text to compare
    # (multiple choice). True/False has nothing to compare, and short answer
    # already gets its own tailored feedback from grade_short_answer().
    if question_data.get("type", "multiple_choice") != "multiple_choice":
        return base if not evidence else f"{base} Evidence: {evidence}"

    if not selected_option or selected_option == correct_option:
        combined = base if not evidence else f"{base} Evidence: {evidence}"
        return combined.strip()

    chosen_text = normalize_quiz_sentence(question_data.get("choices", {}).get(selected_option, ""))
    topic = clean_topic_phrase(extract_focus_phrase(correct_text))
    wrong_focus = clean_topic_phrase(extract_focus_phrase(chosen_text)) if chosen_text else "a different detail"

    comparison = (
        f" Your answer is less accurate because it focuses on {wrong_focus.lower()} instead of the passage's main point about {topic.lower()}."
    )
    evidence_text = f" Evidence: {evidence}" if evidence else ""
    combined = (base + comparison + evidence_text).strip()
    sentences = [s.strip() for s in split_into_sentences(combined) if s.strip()]
    if len(sentences) > 4:
        combined = " ".join(sentences[:4])
    return combined


def score_passage_chunk(sentences: list[str]) -> float:
    if len(sentences) < 4:
        return -1.0

    adjacent_overlap = 0.0
    overlap_pairs = 0
    for idx in range(len(sentences) - 1):
        adjacent_overlap += jaccard_similarity(sentences[idx], sentences[idx + 1])
        overlap_pairs += 1

    avg_overlap = adjacent_overlap / max(overlap_pairs, 1)
    avg_length = sum(len(s.split()) for s in sentences) / max(len(sentences), 1)
    return (len(sentences) * 3.0) + (avg_overlap * 6.0) - abs(avg_length - 18) * 0.08


def select_quiz_passage_chunk(sentences: list[str], min_chunk_sentences: int = 4, max_chunk_sentences: int = 6) -> list[str]:
    """Pick one small, coherent local passage for quiz generation."""
    if len(sentences) <= max_chunk_sentences:
        return sentences

    best_chunk = []
    best_score = -1.0

    for chunk_size in range(min_chunk_sentences, max_chunk_sentences + 1):
        for start_idx in range(0, len(sentences) - chunk_size + 1):
            chunk = sentences[start_idx:start_idx + chunk_size]
            score = score_passage_chunk(chunk)
            if score > best_score:
                best_score = score
                best_chunk = chunk

    return best_chunk or sentences[:max_chunk_sentences]


# ===============================
# AI-based quiz + flashcard generation
# Tries Gemini (cloud, fast) first, then a local Ollama model (free, private,
# but slow on CPU-only hardware), then falls back to the instant local
# pattern-matching generator if neither AI backend is available.
# ===============================
GEMINI_API_URL = "https://generativelanguage.googleapis.com/v1beta/interactions"
# "gemini-3.8-flash" is Google's current headline model, but it was returning
# 503 "high demand" errors consistently in testing. "gemini-flash-lite-latest"
# always auto-points at Google's newest stable Flash-Lite release, answered
# reliably in ~2-5 seconds, and produced flashcards/quiz questions just as
# well-written - so it's used instead.
GEMINI_MODEL = "gemini-flash-lite-latest"
GEMINI_TIMEOUT_SECONDS = 60


def _get_gemini_api_key():
    """Returns the configured Gemini key, or None if it isn't set up.

    Never raises - a missing .streamlit/secrets.toml (e.g. on a machine that
    hasn't configured Gemini) is a normal "not configured" case, not an error.
    """
    try:
        return st.secrets.get("GEMINI_API_KEY")
    except Exception:
        return None


def _call_gemini(prompt: str, schema: dict):
    """POSTs one prompt to the Gemini Interactions API and returns the parsed
    JSON response body (matching `schema`), or None on any failure - missing
    key, network error, bad response shape, invalid JSON, etc. - so callers
    can fall back to another generator without crashing the app."""
    api_key = _get_gemini_api_key()
    if not api_key:
        return None

    try:
        response = requests.post(
            GEMINI_API_URL,
            headers={
                "x-goog-api-key": api_key,
                "Content-Type": "application/json",
            },
            json={
                "model": GEMINI_MODEL,
                "input": prompt,
                "response_format": {
                    "type": "text",
                    "mime_type": "application/json",
                    "schema": schema,
                },
            },
            timeout=GEMINI_TIMEOUT_SECONDS,
        )
        response.raise_for_status()
        body = response.json()

        text = None
        for step in body.get("steps", []):
            if step.get("type") != "model_output":
                continue
            for piece in step.get("content", []):
                if piece.get("type") == "text":
                    text = piece.get("text")
                    break
            if text is not None:
                break
        if text is None:
            return None

        return json.loads(text)
    except Exception:
        return None


OLLAMA_HOST = "http://127.0.0.1:11434"
# llama3.2:3b gives slightly richer prose but is far too slow for interactive
# use on CPU-only hardware (~25 min for 8 flashcards, well past the timeout
# below, which made it silently fall back to the local generator every time).
# llama3.2:1b runs the same JSON-schema-constrained generation in ~3 min with
# still-solid quality, so it's used for both quizzes and flashcards.
OLLAMA_MODEL = "llama3.2:1b"
OLLAMA_TIMEOUT_SECONDS = 600


# Maps the user-facing "Preferred Question Types" labels (as stored in
# settings.json) to the internal type keys used throughout quiz generation,
# validation, and rendering.
QUESTION_TYPE_KEYS = {
    "Multiple Choice": "multiple_choice",
    "True/False": "true_false",
    "Short Answer": "short_answer",
}


def _is_valid_ai_quiz_item(item, allowed_type_keys) -> bool:
    """Structural validation for one AI-generated quiz question. Unlike the
    local generator's validators, this doesn't check for overlap with a
    source sentence - the AI writes original phrasing, not extracted text."""
    if not isinstance(item, dict):
        return False

    question = item.get("question")
    item_type = item.get("type")
    correct = item.get("correct_answer")

    if not isinstance(question, str) or not question.strip():
        return False
    if len(question.strip()) > 300:
        return False
    if item_type not in allowed_type_keys:
        return False

    if item_type == "multiple_choice":
        choices = item.get("choices")
        if not isinstance(choices, dict) or set(choices.keys()) != {"A", "B", "C", "D"}:
            return False
        values = []
        for v in choices.values():
            if not isinstance(v, str) or not v.strip() or len(v.strip().split()) < 2:
                return False
            values.append(v.strip().lower())
        if len(set(values)) != 4:
            return False
        if not isinstance(correct, str) or correct.strip().upper() not in {"A", "B", "C", "D"}:
            return False
    elif item_type == "true_false":
        if not isinstance(correct, str) or correct.strip().lower() not in {"true", "false"}:
            return False
    else:  # short_answer
        if not isinstance(correct, str) or not (1 <= len(correct.strip()) <= 200):
            return False

    return True


def _excerpt_for_prompt(text: str, limit: int = 6000) -> str:
    """Collapses whitespace and caps text at a sentence boundary near `limit`
    chars, so prompts stay a predictable size regardless of note length."""
    excerpt = re.sub(r"\s+", " ", text).strip()
    if len(excerpt) > limit:
        excerpt = excerpt[:limit]
        boundary = max(excerpt.rfind("."), excerpt.rfind("!"), excerpt.rfind("?"))
        if boundary > 1000:
            excerpt = excerpt[:boundary + 1]
    return excerpt


_DIFFICULTY_GUIDANCE = {
    "Easy": "Ask about clear, directly-stated facts. Wrong options (where applicable) should be obviously "
            "incorrect to anyone who read the notes.",
    "Medium": "Require connecting two related ideas from the notes, not just recalling one isolated fact. "
              "Wrong options (where applicable) should be plausible enough to need real understanding to rule out.",
    "Hard": "Require synthesizing or interpreting multiple parts of the notes, not just locating one sentence. "
            "Wrong options (where applicable) should be subtly wrong and easy to confuse with the correct one.",
}

_EXPLANATION_LEVEL_GUIDANCE = {
    "Simple": "Explanations must be one short, plain-language sentence a beginner could follow, with no jargon.",
    "Standard": "Explanations should be one to two clear sentences, correct but not overly technical.",
    "Advanced": "Explanations may use precise, technical, or domain-specific language and note subtler reasoning.",
}

_ANSWER_LENGTH_GUIDANCE = {
    "Concise": "Keep each explanation to a single short sentence.",
    "Detailed": "Explanations may be two to three sentences if useful for understanding.",
}


def _build_quiz_prompt_and_schema(
    text: str,
    max_questions: int,
    question_types=None,
    difficulty: str = "Medium",
    explanation_level: str = "Standard",
    answer_length: str = "Detailed",
):
    excerpt = _excerpt_for_prompt(text)
    question_types = question_types or ["Multiple Choice"]
    allowed_type_keys = [QUESTION_TYPE_KEYS[t] for t in question_types if t in QUESTION_TYPE_KEYS] or ["multiple_choice"]

    type_instructions = {
        "multiple_choice": (
            '"multiple_choice": set "choice_a".."choice_d" to four complete, well-written answer options '
            '(exactly one correct, the rest plausible but clearly wrong), and "correct_answer" to the letter '
            '(A, B, C, or D) of the correct one. Do not copy the correct answer verbatim from the notes - '
            "rephrase it in your own words while keeping it accurate."
        ),
        "true_false": (
            '"true_false": write a statement (not a question) in the "question" field that is either true or '
            'false according to the notes, leave "choice_a".."choice_d" as empty strings, and set '
            '"correct_answer" to exactly "True" or "False".'
        ),
        "short_answer": (
            '"short_answer": write an open-ended question in the "question" field, leave "choice_a".."choice_d" '
            'as empty strings, and set "correct_answer" to a short reference answer (a few words to one '
            "sentence) that a grader can compare a student's free-text answer against."
        ),
    }
    types_block = "\n".join(f"- {type_instructions[t]}" for t in allowed_type_keys)
    type_list_label = " / ".join(allowed_type_keys)

    prompt = f"""You are creating a reading comprehension quiz from study notes.

Generate exactly {max_questions} questions based only on the notes below, using ONLY these question
types: {type_list_label}. If more than one type is listed, spread the questions reasonably evenly across
them. Every item needs a "type" field set to one of: {type_list_label}.

Difficulty level - {difficulty}: {_DIFFICULTY_GUIDANCE[difficulty]}

For each question's "type", fill the fields this way:
{types_block}

Explanation style: {_EXPLANATION_LEVEL_GUIDANCE[explanation_level]} {_ANSWER_LENGTH_GUIDANCE[answer_length]}
Every item needs a one-to-few-sentence "explanation" of why the correct answer is right, following that style.

Write every question and explanation in proper English with correct grammar and spelling.

STUDY NOTES:
\"\"\"
{excerpt}
\"\"\"
"""

    # A small model won't reliably honor "return N items" as free text, so the
    # array length is enforced structurally via a JSON schema (constrained
    # decoding) rather than left to the model to get right on its own. All
    # three question types share one flat shape (rather than a oneOf/union)
    # because constrained decoding support for schema unions is inconsistent
    # across the Gemini/Ollama backends this app uses - unused fields (e.g.
    # choice_a-d for a short_answer item) are just instructed to be "".
    quiz_schema = {
        "type": "array",
        "minItems": max_questions,
        "maxItems": max_questions,
        "items": {
            "type": "object",
            "properties": {
                "type": {"type": "string", "enum": allowed_type_keys},
                "question": {"type": "string"},
                "choice_a": {"type": "string"},
                "choice_b": {"type": "string"},
                "choice_c": {"type": "string"},
                "choice_d": {"type": "string"},
                "correct_answer": {"type": "string"},
                "explanation": {"type": "string"},
            },
            "required": [
                "type", "question", "choice_a", "choice_b", "choice_c", "choice_d",
                "correct_answer", "explanation",
            ],
        },
    }
    return prompt, quiz_schema, allowed_type_keys


def _parse_ai_quiz_items(parsed, max_questions: int, allowed_type_keys):
    if not isinstance(parsed, list):
        return None

    questions = []
    seen_questions = set()
    for item in parsed:
        if len(questions) >= max_questions:
            break
        if not _is_valid_ai_quiz_item(item, allowed_type_keys):
            continue

        question_key = simplify_text_key(item["question"])
        if question_key in seen_questions:
            continue
        seen_questions.add(question_key)

        item_type = item["type"]
        if item_type == "multiple_choice":
            choices = {
                "A": item["choice_a"].strip(),
                "B": item["choice_b"].strip(),
                "C": item["choice_c"].strip(),
                "D": item["choice_d"].strip(),
            }
            correct_answer = item["correct_answer"].strip().upper()
        elif item_type == "true_false":
            choices = {"True": "True", "False": "False"}
            correct_answer = "True" if item["correct_answer"].strip().lower() == "true" else "False"
        else:  # short_answer
            choices = {}
            correct_answer = item["correct_answer"].strip()

        questions.append({
            "type": item_type,
            "question": item["question"].strip(),
            "choices": choices,
            "correctAnswer": correct_answer,
            "explanation": str(item.get("explanation", "")).strip(),
            "evidence": "",
        })

    return questions if questions else None


def generate_quiz_with_gemini(
    text: str, max_questions: int = 10, question_types=None,
    difficulty: str = "Medium", explanation_level: str = "Standard", answer_length: str = "Detailed",
):
    """Quiz generator backed by the Gemini API (cloud). Returns None (not
    []) if the key isn't configured or the call fails for any reason."""
    if not text or not text.strip():
        return None
    prompt, schema, allowed_type_keys = _build_quiz_prompt_and_schema(
        text, max_questions, question_types, difficulty, explanation_level, answer_length
    )
    parsed = _call_gemini(prompt, schema)
    return _parse_ai_quiz_items(parsed, max_questions, allowed_type_keys)


def generate_quiz_with_ai(
    text: str, max_questions: int = 10, question_types=None,
    difficulty: str = "Medium", explanation_level: str = "Standard", answer_length: str = "Detailed",
):
    """
    Quiz generator backed by a local Ollama model (e.g. llama3.2:1b). Runs
    entirely on-device - no cloud API, no cost. Returns None (not []) on any
    failure, so the caller can tell "AI unavailable" apart from "AI ran but
    the note had nothing quiz-worthy in it."
    """
    if not text or not text.strip():
        return None

    prompt, quiz_schema, allowed_type_keys = _build_quiz_prompt_and_schema(
        text, max_questions, question_types, difficulty, explanation_level, answer_length
    )

    try:
        response = requests.post(
            f"{OLLAMA_HOST}/api/generate",
            json={
                "model": OLLAMA_MODEL,
                "prompt": prompt,
                "stream": False,
                "format": quiz_schema,
                "options": {"temperature": 0.4},
            },
            timeout=OLLAMA_TIMEOUT_SECONDS,
        )
        response.raise_for_status()
        raw = response.json().get("response", "")
        parsed = json.loads(raw)
    except Exception:
        return None

    return _parse_ai_quiz_items(parsed, max_questions, allowed_type_keys)


def generate_quiz(
    text: str, max_questions: int = 10, question_types=None,
    difficulty: str = "Medium", explanation_level: str = "Standard", answer_length: str = "Detailed",
    shuffle: bool = True,
):
    """Try Gemini first (fast, cloud), then the local Ollama model (free,
    private, but slow on CPU-only hardware), then fall back to the instant
    free heuristic generator if neither AI backend is available.

    An AI response can legitimately come back short of max_questions - one
    item might fail validation or two questions can simplify to the same
    dedup key - and previously that partial result was just accepted as-is.
    Any shortfall is now topped up from the local generator (skipping
    questions the AI already asked) so the caller always gets max_questions
    questions whenever the note has enough content to support that many,
    regardless of which backend produced them.

    The local top-up generator only ever produces multiple-choice questions
    (it's a sentence-matching heuristic, not an AI, so true/false and
    short-answer generation aren't practical to build into it) - it's used
    regardless of `question_types` since partial multiple-choice coverage
    beats stopping short of max_questions entirely.

    Returns (questions, source) where source is "ai" (came only/mostly from
    an AI backend) or "local" (AI unavailable, all questions from the local
    generator).
    """
    ai_questions = generate_quiz_with_gemini(
        text, max_questions=max_questions, question_types=question_types,
        difficulty=difficulty, explanation_level=explanation_level, answer_length=answer_length,
    ) or []
    if not ai_questions:
        # Only fall through to the slow local model when Gemini produced
        # nothing at all - not just to top up a partial Gemini result, since
        # that would trade Gemini's few-second turnaround for Ollama's
        # multi-minute one just to fetch one or two extra questions.
        ai_questions = generate_quiz_with_ai(
            text, max_questions=max_questions, question_types=question_types,
            difficulty=difficulty, explanation_level=explanation_level, answer_length=answer_length,
        ) or []

    source = "ai" if ai_questions else "local"

    if len(ai_questions) < max_questions:
        existing_keys = {simplify_text_key(q["question"]) for q in ai_questions}
        # Ask for extra headroom so there's enough non-overlapping material
        # left over after skipping questions the AI already asked.
        local_questions = generate_quiz_from_text(text, max_questions=max_questions * 2)
        for question in local_questions:
            if len(ai_questions) >= max_questions:
                break
            key = simplify_text_key(question["question"])
            if key in existing_keys:
                continue
            existing_keys.add(key)
            ai_questions.append(question)

    questions = ai_questions[:max_questions]
    if shuffle:
        random.shuffle(questions)
    return questions, source


def _is_valid_ai_flashcard_item(item) -> bool:
    """Structural validation for one AI-generated flashcard."""
    if not isinstance(item, dict):
        return False

    q = item.get("q")
    a = item.get("a")

    if not isinstance(q, str) or len(q.strip()) < 10 or len(q.strip()) > 300:
        return False
    if not isinstance(a, str) or len(a.strip().split()) < 6 or len(a.strip()) > 700:
        return False

    return True


def _build_flashcard_prompt_and_schema(
    text: str, max_cards: int,
    explanation_level: str = "Standard", answer_length: str = "Detailed", auto_examples: bool = False,
):
    excerpt = _excerpt_for_prompt(text)

    answer_length_line = (
        "- The answer should be a complete, clear explanation in one to two sentences - correct and "
        "useful, but no longer than necessary."
        if answer_length == "Concise" else
        "- The answer must be a complete, clear explanation a student could actually learn from - several "
        "full sentences, not a sentence fragment lifted verbatim from the text."
    )
    example_line = (
        "- Where it would genuinely help understanding, include a brief concrete example in the answer."
        if auto_examples else ""
    )

    prompt = f"""You are creating study flashcards from a student's notes.

Generate exactly {max_cards} flashcards based only on the notes below. For each flashcard:
- Write a substantive question that tests real understanding of an idea, event, or relationship in the
  notes - never a trivial one- or two-word question about a single stray word or heading.
- The question should be a full, well-formed sentence in proper English with correct grammar and
  spelling, long enough to give real context (roughly one to two sentences).
{answer_length_line}
{example_line}
- {_EXPLANATION_LEVEL_GUIDANCE[explanation_level]}
- Rephrase ideas in your own original words rather than copying the notes verbatim; keep it accurate.
- Cover a range of different ideas from across the notes rather than repeating the same point.

STUDY NOTES:
\"\"\"
{excerpt}
\"\"\"
"""

    flashcard_schema = {
        "type": "array",
        "minItems": max_cards,
        "maxItems": max_cards,
        "items": {
            "type": "object",
            "properties": {
                "q": {"type": "string"},
                "a": {"type": "string"},
            },
            "required": ["q", "a"],
        },
    }
    return prompt, flashcard_schema


def _parse_ai_flashcard_items(parsed, max_cards: int):
    if not isinstance(parsed, list):
        return None

    cards = []
    seen_questions = set()
    for item in parsed:
        if len(cards) >= max_cards:
            break
        if not _is_valid_ai_flashcard_item(item):
            continue

        question_key = simplify_text_key(item["q"])
        if question_key in seen_questions:
            continue
        seen_questions.add(question_key)

        cards.append({"q": item["q"].strip(), "a": item["a"].strip()})

    return cards if cards else None


def generate_flashcards_with_gemini(
    text: str, max_cards: int = 8,
    explanation_level: str = "Standard", answer_length: str = "Detailed", auto_examples: bool = False,
):
    """Flashcard generator backed by the Gemini API (cloud). Returns None
    (not []) if the key isn't configured or the call fails for any reason."""
    if not text or not text.strip():
        return None
    prompt, schema = _build_flashcard_prompt_and_schema(text, max_cards, explanation_level, answer_length, auto_examples)
    parsed = _call_gemini(prompt, schema)
    return _parse_ai_flashcard_items(parsed, max_cards)


def generate_flashcards_with_ai(
    text: str, max_cards: int = 8,
    explanation_level: str = "Standard", answer_length: str = "Detailed", auto_examples: bool = False,
):
    """Flashcard generator backed by the same local Ollama model used for the
    quiz. Returns None (not []) on any failure, so the caller can tell "AI
    unavailable" apart from "AI ran but found nothing flashcard-worthy"."""
    if not text or not text.strip():
        return None

    prompt, flashcard_schema = _build_flashcard_prompt_and_schema(text, max_cards, explanation_level, answer_length, auto_examples)

    try:
        response = requests.post(
            f"{OLLAMA_HOST}/api/generate",
            json={
                "model": OLLAMA_MODEL,
                "prompt": prompt,
                "stream": False,
                "format": flashcard_schema,
                "options": {"temperature": 0.4},
            },
            timeout=OLLAMA_TIMEOUT_SECONDS,
        )
        response.raise_for_status()
        raw = response.json().get("response", "")
        parsed = json.loads(raw)
    except Exception:
        return None

    return _parse_ai_flashcard_items(parsed, max_cards)


def generate_flashcards(
    text: str, max_cards: int = 8,
    explanation_level: str = "Standard", answer_length: str = "Detailed", auto_examples: bool = False,
):
    """Try Gemini first (fast, cloud), then the local Ollama model (free,
    private, but slow on CPU-only hardware), then fall back to the instant
    free heuristic generator if neither AI backend is available.

    An AI response can legitimately come back short of max_cards - one of its
    items might fail validation (answer too short, etc.) or two questions can
    simplify to the same dedup key - and previously that partial result was
    just accepted as-is. Any shortfall is now topped up from the local
    generator (skipping topics the AI already covered) so the caller always
    gets max_cards cards whenever the note has enough content to support
    that many, regardless of which backend produced them.

    explanation_level/answer_length/auto_examples only shape AI-written
    answers - the local heuristic generator pulls its answers verbatim from
    the note's own text, so it has no "style" to steer.

    Returns (cards, source) where source is "ai" (came only/mostly from an AI
    backend) or "local" (AI unavailable, all cards from the local generator).
    """
    ai_cards = generate_flashcards_with_gemini(
        text, max_cards=max_cards, explanation_level=explanation_level,
        answer_length=answer_length, auto_examples=auto_examples,
    ) or []
    if not ai_cards:
        # Only fall through to the slow local model when Gemini produced
        # nothing at all - not just to top up a partial Gemini result, since
        # that would trade Gemini's few-second turnaround for Ollama's
        # multi-minute one just to fetch one or two extra cards.
        ai_cards = generate_flashcards_with_ai(
            text, max_cards=max_cards, explanation_level=explanation_level,
            answer_length=answer_length, auto_examples=auto_examples,
        ) or []

    source = "ai" if ai_cards else "local"

    if len(ai_cards) < max_cards:
        existing_keys = {simplify_text_key(c["q"]) for c in ai_cards}
        # Ask for extra headroom so there's enough non-overlapping material
        # left over after skipping topics the AI already covered.
        local_cards = generate_flashcards_from_text(text, max_cards=max_cards * 2)
        for card in local_cards:
            if len(ai_cards) >= max_cards:
                break
            key = simplify_text_key(card["q"])
            if key in existing_keys:
                continue
            existing_keys.add(key)
            ai_cards.append(card)

    return ai_cards[:max_cards], source


def _grade_short_answer_locally(reference_answer: str, user_answer: str) -> bool:
    """Heuristic fallback when Gemini grading is unavailable. Exact string
    equality is too strict for free-text answers (correct answers are often
    worded differently from the reference), so this instead checks how much
    of the reference answer's meaningful (3+ letter) vocabulary shows up
    somewhere in the student's answer."""
    def normalize(s):
        return re.sub(r"[^\w\s]", "", s.lower()).split()

    ref_words = {w for w in normalize(reference_answer) if len(w) > 2}
    user_words = set(normalize(user_answer))
    if not ref_words:
        return normalize(reference_answer) == normalize(user_answer)
    return len(ref_words & user_words) / len(ref_words) >= 0.6


def grade_short_answer(question: str, reference_answer: str, user_answer: str):
    """Judges a free-text quiz answer. Tries Gemini first for a real semantic
    read (a correct answer can be worded completely differently from the
    reference), falling back to the local word-overlap heuristic above if
    Gemini isn't configured or the call fails - Ollama is deliberately not
    used here even as a second AI attempt, since grading happens inline while
    the user is waiting on one question, and Ollama's multi-minute latency on
    this machine would make that wait feel broken.

    Returns (is_correct: bool, feedback: str).
    """
    if not user_answer or not user_answer.strip():
        return False, "No answer was submitted."

    prompt = f"""A student was asked this short-answer study question:
"{question}"

Reference answer: "{reference_answer}"
Student's answer: "{user_answer}"

Judge whether the student's answer is substantively correct, even if worded differently from the
reference answer - minor wording differences are fine as long as the core idea is right. Then write one
short, encouraging sentence of feedback explaining why.
"""
    schema = {
        "type": "object",
        "properties": {
            "is_correct": {"type": "boolean"},
            "feedback": {"type": "string"},
        },
        "required": ["is_correct", "feedback"],
    }
    result = _call_gemini(prompt, schema)
    if (
        isinstance(result, dict)
        and isinstance(result.get("is_correct"), bool)
        and isinstance(result.get("feedback"), str)
        and result["feedback"].strip()
    ):
        return result["is_correct"], result["feedback"].strip()

    is_correct = _grade_short_answer_locally(reference_answer, user_answer)
    feedback = (
        "That covers the key point from the reference answer." if is_correct
        else f"The reference answer was: {reference_answer}"
    )
    return is_correct, feedback


def generate_quiz_from_text(text: str, max_questions: int = 10):
    """
    FREE/local quiz generator (no API).
    Creates multiple-choice questions from the cleaned passage text.
    """
    if not text or not text.strip():
        return []

    cleaned = clean_extracted_text(text)
    cleaned = re.sub(r"\s+", " ", cleaned).strip()
    sentences = split_into_sentences(cleaned)

    # Normalize + dedupe source sentences to reduce repeated options across questions.
    good_sentences = []
    seen_sentence_norm = set()
    for s in sentences:
        s = normalize_quiz_sentence(s.strip().strip("â€¢-â€” "))
        if not is_good_quiz_source_sentence(s):
            continue
        k = s.lower()
        if k not in seen_sentence_norm:
            good_sentences.append(s)
            seen_sentence_norm.add(k)

    if len(good_sentences) < 4:
        return []

    # Prefer one coherent local passage first (keeps early questions topically
    # clustered), then fall back to the rest of the document's good sentences so
    # we aren't capped at a single small passage when the note has plenty more
    # usable content and max_questions hasn't been reached yet.
    selected_chunk = select_quiz_passage_chunk(good_sentences, min_chunk_sentences=4, max_chunk_sentences=6)
    chunk_set = set(selected_chunk)
    remaining_sentences = [s for s in good_sentences if s not in chunk_set]

    def by_priority(sentences):
        return sorted(
            sentences,
            key=lambda s: (comprehension_priority_score(s), len(s)),
            reverse=True,
        )

    candidate_sentences = by_priority(selected_chunk) + by_priority(remaining_sentences)

    questions = []
    used_questions = set()

    for idx, sentence in enumerate(candidate_sentences):
        if len(questions) >= max_questions:
            break

        question = build_quiz_question(sentence, good_sentences, idx)
        if not question:
            continue

        # Dedupe by the underlying evidence sentence, not the question wording -
        # question text is drawn from a small set of templates and legitimately
        # repeats across genuinely different content.
        question_key = simplify_text_key(question["evidence"])
        if question_key in used_questions:
            continue

        used_questions.add(question_key)
        questions.append(question)

    return questions


def render_quiz_feedback_card(title: str, body: str):
    st.markdown(
        f"""
        <div class="quiz-explanation-card">
            <div class="quiz-explanation-title">{html.escape(title)}</div>
            <div class="quiz-explanation-body">{html.escape(body)}</div>
        </div>
        """,
        unsafe_allow_html=True,
    )


def get_question_topic(question_data: dict, fallback_label: str = "Question") -> str:
    evidence = normalize_quiz_sentence(question_data.get("evidence", "") or question_data.get("source_sentence", ""))
    # Multiple choice: the correct option's own text is usually the most
    # on-topic summary available. True/false and short answer have no
    # comparable option text (a choices dict of {} or {"True": "True", ...}
    # isn't descriptive), so those fall back to the question/evidence text.
    correct_text = ""
    if question_data.get("type", "multiple_choice") == "multiple_choice":
        correct_option = question_data.get("correctAnswer") or question_data.get("correct_answer")
        correct_text = normalize_quiz_sentence(question_data.get("choices", {}).get(correct_option, ""))
    source_text = correct_text or evidence or question_data.get("question", fallback_label)
    return clean_topic_phrase(extract_focus_phrase(source_text))


def render_quiz_option_summary(question: dict, selected_option: str, option_keys=None):
    correct_option = question.get("correctAnswer") or question.get("correct_answer")
    for option_key in (option_keys or ["A", "B", "C", "D"]):
        state = "neutral"
        if option_key == correct_option:
            state = "correct"
        if option_key == selected_option and option_key != correct_option:
            state = "incorrect"

        # Badge shows just the first letter (A/B/C/D, or T/F for true-false) -
        # for true/false the full word is the option text too, so spelling it
        # out again in the small round badge would just be redundant.
        st.markdown(
            f"""
            <div class="quiz-option-card quiz-option-{state}">
                <div class="quiz-option-badge">{option_key[0]}</div>
                <div class="quiz-option-text">{html.escape(question['choices'][option_key])}</div>
            </div>
            """,
            unsafe_allow_html=True,
        )
def _persisting() -> bool:
    """Only signed-in users have anything saved. Guests use the app with
    in-memory state that disappears with the session, so every save_* below
    is a no-op for them."""
    return bool(st.session_state.get("authenticated"))


def load_notes():
    """Load saved notes from notes.json"""
    if not os.path.exists(NOTES_JSON):
        return {}
    try:
        with open(NOTES_JSON, "r", encoding="utf-8") as f:
            return json.load(f)
    except json.JSONDecodeError:
        return {}


def save_notes(notes: dict):
    """Save notes to notes.json"""
    if not _persisting():
        return
    with open(NOTES_JSON, "w", encoding="utf-8") as f:
        json.dump(notes, f, indent=2, ensure_ascii=False)


# ---- Study streak -------------------------------------------------------
# The streak is never stored as a number. What is stored is the list of days
# the user really studied (a day counts when a quiz is finished), and the
# streak is worked out from those days whenever it is shown. That way it can't
# go stale: skip a day and it drops to 0 by itself.

def _parse_study_day(value):
    """Turn '2026-02-19' or '2026-02-19T13:55:34' into a date, or None if it isn't one."""
    if not isinstance(value, str):
        return None
    try:
        return date.fromisoformat(value[:10])
    except ValueError:
        return None


def calculate_streak(study_days, today=None):
    """Number of consecutive study days ending today (or yesterday, if the
    user just hasn't studied yet today). 0 if the last study day is older."""
    today = today or date.today()
    days = {d for d in study_days if d <= today}  # ignore dates in the future
    if today in days:
        cursor = today
    elif today - timedelta(days=1) in days:
        cursor = today - timedelta(days=1)
    else:
        return 0
    streak = 0
    while cursor in days:
        streak += 1
        cursor -= timedelta(days=1)
    return streak


def load_streak():
    """Load the days the user studied, as {"study_dates": ["YYYY-MM-DD", ...]}.

    Days come from streak_data.json plus the dated quiz results already saved
    on each note (real records), so nothing is invented and old data is kept.
    """
    days = set()
    stored = None
    if os.path.exists(STREAK_JSON):
        try:
            with open(STREAK_JSON, "r", encoding="utf-8") as f:
                stored = json.load(f)
            if isinstance(stored, dict):
                # "last_study_date" is from the old format, which stored a counter.
                for value in list(stored.get("study_dates") or []) + [stored.get("last_study_date")]:
                    parsed = _parse_study_day(value)
                    if parsed:
                        days.add(parsed)
        except (json.JSONDecodeError, OSError):
            pass
    for note in load_notes().values():
        for attempt in note.get("quiz_history", []):
            parsed = _parse_study_day(attempt.get("date"))
            if parsed:
                days.add(parsed)
    data = {"study_dates": sorted(d.isoformat() for d in days)}
    if stored != data:
        save_streak(data)  # also upgrades an old-format file
    return data


def save_streak(data: dict):
    """Save streak data to streak_data.json (written safely so a crash can't corrupt it)."""
    if not _persisting():
        return
    temp_path = STREAK_JSON + ".tmp"
    with open(temp_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
    os.replace(temp_path, STREAK_JSON)


def record_study_day(data: dict, today=None):
    """Record that the user studied today. Returns True if today wasn't recorded yet."""
    today_iso = (today or date.today()).isoformat()
    if today_iso in data["study_dates"]:
        return False
    data["study_dates"] = sorted(set(data["study_dates"]) | {today_iso})
    save_streak(data)
    return True


def streak_summary(data: dict, today=None):
    """Everything the screen needs: current streak, whether today is done, last study day."""
    today = today or date.today()
    days = [d for d in (_parse_study_day(v) for v in data.get("study_dates", [])) if d and d <= today]
    return {
        "streak": calculate_streak(days, today),
        "studied_today": today in days,
        "last_day": max(days) if days else None,
    }


def streak_message(data: dict, today=None):
    """One honest line describing the study streak."""
    info = streak_summary(data, today)
    streak = info["streak"]
    if streak == 0:
        if info["last_day"]:
            last = f"{info['last_day']:%B} {info['last_day'].day}, {info['last_day'].year}"
            return f"🔥 **Study Streak: 0 days** · last studied {last}. Finish a quiz to start a new streak."
        return "🔥 **Study Streak: 0 days** · Finish a quiz to start your streak."
    day_word = "day" if streak == 1 else "days"
    if info["studied_today"]:
        return f"🔥 **Study Streak: {streak} {day_word}**"
    return f"🔥 **Study Streak: {streak} {day_word}** · Finish a quiz today to keep it going."


# ---- Settings --------------------------------------------------------------
SETTINGS_JSON = os.path.join(DATA_DIR, "settings.json")

# Single source of truth for every setting: its default and the values it's
# allowed to hold. load_settings() validates against this on every load, so a
# hand-edited or stale settings.json can never hand the rest of the app a
# value it doesn't know how to handle.
QUIZ_DIFFICULTIES = ["Easy", "Medium", "Hard"]
QUESTION_COUNT_OPTIONS = [5, 10, 15, 20]
FLASHCARD_COUNT_OPTIONS = [5, 10, 15, 20]
QUESTION_TYPE_OPTIONS = ["Multiple Choice", "True/False", "Short Answer"]
EXPLANATION_LEVELS = ["Simple", "Standard", "Advanced"]
ANSWER_LENGTHS = ["Concise", "Detailed"]
THEME_OPTIONS = ["Light", "Dark", "System Default"]

SETTINGS_DEFAULTS = {
    "display_name": "",
    "quiz_difficulty": "Medium",
    "quiz_question_count": 10,
    "flashcard_count": 10,
    "question_types": ["Multiple Choice"],
    "shuffle_questions": True,
    "explanation_level": "Standard",
    "answer_length": "Detailed",
    "auto_examples": False,
    "theme": "Dark",
}


def load_settings() -> dict:
    """Loads settings.json, validating every field against SETTINGS_DEFAULTS
    so a missing file, a missing key (e.g. after an app update added a new
    setting), or a hand-edited bad value all safely fall back to a sensible
    default instead of breaking the app."""
    data = {}
    if os.path.exists(SETTINGS_JSON):
        try:
            with open(SETTINGS_JSON, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            if isinstance(loaded, dict):
                data = loaded
        except (json.JSONDecodeError, OSError):
            pass

    settings = dict(SETTINGS_DEFAULTS)
    settings["display_name"] = str(data.get("display_name", "")).strip()

    if data.get("quiz_difficulty") in QUIZ_DIFFICULTIES:
        settings["quiz_difficulty"] = data["quiz_difficulty"]
    if data.get("quiz_question_count") in QUESTION_COUNT_OPTIONS:
        settings["quiz_question_count"] = data["quiz_question_count"]
    if data.get("flashcard_count") in FLASHCARD_COUNT_OPTIONS:
        settings["flashcard_count"] = data["flashcard_count"]

    raw_types = data.get("question_types")
    if isinstance(raw_types, list):
        valid_types = [t for t in raw_types if t in QUESTION_TYPE_OPTIONS]
        if valid_types:
            settings["question_types"] = valid_types

    if isinstance(data.get("shuffle_questions"), bool):
        settings["shuffle_questions"] = data["shuffle_questions"]
    if data.get("explanation_level") in EXPLANATION_LEVELS:
        settings["explanation_level"] = data["explanation_level"]
    if data.get("answer_length") in ANSWER_LENGTHS:
        settings["answer_length"] = data["answer_length"]
    if isinstance(data.get("auto_examples"), bool):
        settings["auto_examples"] = data["auto_examples"]
    if data.get("theme") in THEME_OPTIONS:
        settings["theme"] = data["theme"]

    return settings


def save_settings(data: dict):
    if not _persisting():
        return
    temp_path = SETTINGS_JSON + ".tmp"
    with open(temp_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    os.replace(temp_path, SETTINGS_JSON)


# ---- Authentication ---------------------------------------------------------
# This is a single-user local app, so "accounts" means exactly one stored
# account - signing up once, then signing back in with that same email/
# password on every later visit. There's no password-reset flow; if the
# password is lost, data/users.json would need to be deleted manually to
# start over (this is a locally-run personal app, not a hosted multi-user
# service, so that tradeoff is reasonable here).
USERS_JSON = os.path.join(DATA_DIR, "users.json")
_PBKDF2_ITERATIONS = 200_000


def _hash_password(password: str, salt: bytes = None):
    """PBKDF2-HMAC-SHA256 with a random salt - stdlib only (hashlib), so no
    new dependency like bcrypt/passlib is needed for this single-account use
    case. Returns (salt_hex, hash_hex)."""
    if salt is None:
        salt = os.urandom(16)
    pwd_hash = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, _PBKDF2_ITERATIONS)
    return salt.hex(), pwd_hash.hex()


def load_user():
    """Returns the single stored account dict, or None if no account has
    been created yet (i.e. the app should show the sign-up form)."""
    if os.path.exists(USERS_JSON):
        try:
            with open(USERS_JSON, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict) and data.get("email") and data.get("salt") and data.get("password_hash"):
                return data
        except (json.JSONDecodeError, OSError):
            pass
    return None


def _account_identity():
    """(full_name, email) of whoever is signed in, from the account itself.

    Signed in with Google or Microsoft: the full name on that account - the
    provider's "name" claim, or given + family name when the provider sends the
    parts separately. Signed up here with email and password: the first and last
    name entered at sign-up. Either may be "" if the account doesn't have one.
    """
    name = email = ""
    try:
        if st.user.is_logged_in:
            name = str(st.user.get("name") or "").strip()
            given = str(st.user.get("given_name") or "").strip()
            family = str(st.user.get("family_name") or "").strip()
            if given and family and len(name.split()) < 2:
                name = f"{given} {family}"
            elif not name:
                name = given
            email = str(st.user.get("email") or "").strip()
    except AttributeError:
        pass  # auth isn't configured at all - st.user has no attributes
    if not name:
        account = load_user()
        if account:
            name = f"{account.get('first_name', '')} {account.get('last_name', '')}".strip()
            email = email or account.get("email", "")
    return name, email


def create_user(first_name: str, last_name: str, email: str, password: str) -> dict:
    salt_hex, hash_hex = _hash_password(password)
    user = {
        "first_name": first_name.strip(),
        "last_name": last_name.strip(),
        "email": email.strip().lower(),
        "salt": salt_hex,
        "password_hash": hash_hex,
        "created_at": datetime.now().isoformat(),
    }
    temp_path = USERS_JSON + ".tmp"
    with open(temp_path, "w", encoding="utf-8") as f:
        json.dump(user, f, indent=2, ensure_ascii=False)
    os.replace(temp_path, USERS_JSON)
    return user


def verify_user(email: str, password: str) -> bool:
    """True only if an account exists, the email matches it, and the
    password's hash matches - using a constant-time comparison so a
    mismatch's timing doesn't leak how many hash bytes matched."""
    user = load_user()
    if not user or user["email"] != email.strip().lower():
        return False
    salt = bytes.fromhex(user["salt"])
    _, candidate_hash = _hash_password(password, salt)
    return hmac.compare_digest(candidate_hash, user["password_hash"])


def _microsoft_login_configured() -> bool:
    """True once a real Microsoft application (client) ID is filled into secrets.toml's
    [auth.microsoft] section (Azure app registration). Until then the
    Microsoft buttons say it isn't set up instead of calling st.login("microsoft") and
    hitting a StreamlitAuthError."""
    try:
        cfg = st.secrets.get("auth", {}).get("microsoft", {})
        secret = str(cfg.get("client_secret") or "")
        # Both the ID and a real secret must be there - the placeholder text
        # in secrets.toml doesn't count.
        return bool(cfg.get("client_id")) and bool(secret) and not secret.startswith("PASTE_")
    except Exception:
        return False


def _google_login_configured() -> bool:
    """True once a real Google OAuth client_id has been filled into
    secrets.toml's [auth.google] section - until then, the Google button
    shows the same "not set up yet" message Microsoft's does, instead of
    calling st.login("google") and hitting a StreamlitAuthError."""
    try:
        return bool(st.secrets.get("auth", {}).get("google", {}).get("client_id"))
    except Exception:
        return False


# ---- Auth page: image corridor ----------------------------------------------
# A Python port of a React/CSS component (ImageStreamHero): two rails of
# image cards ride a 3D perspective corridor from the horizon toward the
# viewer. The exact depth-easing math matters - see the three numbered notes
# below, ported as-is from the original's design comment, since they're each
# the fix for a specific visual artifact (cards tearing apart, a bend-free
# cone, or a gap blinking open at the center once per loop).
_CORRIDOR_PATH = {
    "perspective": 30, "card_width": 18, "card_height": 25, "card_radius": 0.4,
    "birth_height": 2.6, "exit_height": 46, "rail_birth": -11, "rail_exit": 44,
    "fan": 3.3, "turn_birth": 6, "turn_exit": 28, "stops": 24,
}


def _corridor_keyframes(direction: int, name: str, p: dict) -> str:
    steps = []
    for s in range(p["stops"] + 1):
        u = s / p["stops"]
        # Geometric in apparent size, so consecutive cards keep a constant
        # size ratio and the ribbon stays solid at both ends (note 1).
        scale = (p["birth_height"] / p["card_height"]) * (p["exit_height"] / p["birth_height"]) ** u
        z = p["perspective"] * (1 - 1 / scale)
        # Opens hard early then holds (fan > 1), so the ribbon leaves the
        # centre flat and only bends onto the diagonal once (note 2).
        rail = p["rail_exit"] - (p["rail_exit"] - p["rail_birth"]) * (1 - u) ** p["fan"]
        turn = p["turn_birth"] + (p["turn_exit"] - p["turn_birth"]) * u
        steps.append(
            f"{u * 100:.2f}%{{transform:translate3d({direction * rail:.2f}cqw,0,{z:.2f}cqw) "
            f"rotateY({-direction * turn:.2f}deg)}}"
        )
    return f"@keyframes {name}{{{''.join(steps)}}}"


def render_image_corridor(image_data_uris: list, container_id: str, cards: int = 9, speed: int = 18, axis: int = 55):
    """Renders the corridor into an element with id=`container_id` that the
    caller has already placed in the page. image_data_uris are full
    `data:image/...;base64,...` strings - embedded directly (not served as
    static files) so the page has no dependency on Streamlit's static-file
    URL configuration."""
    p = _CORRIDOR_PATH
    right_name = f"corridor-r-{container_id}"
    left_name = f"corridor-l-{container_id}"
    css = _corridor_keyframes(1, right_name, p) + _corridor_keyframes(-1, left_name, p)

    cards_html = []
    for rail_name, direction in [(right_name, 1), (left_name, -1)]:
        for i in range(cards):
            img = image_data_uris[i % len(image_data_uris)] if image_data_uris else None
            delay = -(i * speed) / cards
            style = (
                f"left:50%;top:{axis}%;width:{p['card_width']}cqw;height:{p['card_height']}cqw;"
                f"margin-left:{-p['card_width'] / 2}cqw;margin-top:{-p['card_height'] / 2}cqw;"
                f"border-radius:{p['card_radius']}cqw;animation:{rail_name} {speed}s linear infinite;"
                f"animation-delay:{delay:.3f}s;backface-visibility:hidden;"
            )
            img_tag = f"<img src='{img}' loading='lazy' decoding='async' draggable='false'/>" if img else ""
            cards_html.append(f"<div class='corridor-card' style='{style}'>{img_tag}</div>")

    return f"""
    <style>{css}</style>
    <div class="corridor-stage" style="perspective:{p['perspective']}cqw;perspective-origin:50% {axis}%;">
        <div class="corridor-space">{''.join(cards_html)}</div>
    </div>
    """


@st.cache_data(show_spinner=False)
def _load_auth_corridor_images() -> list:
    """Base64 data URIs, embedded directly in the page rather than served as
    static files - avoids depending on Streamlit's static-serving URL
    convention, and these are small (~45KB each) after being resized
    specifically for this use."""
    names = ["notes.jpg", "progress.jpg", "thinking.jpg", "quiz.jpg", "celebrate.jpg"]
    base_dir = os.path.join("static", "auth")
    uris = []
    for name in names:
        path = os.path.join(base_dir, name)
        if not os.path.exists(path):
            continue
        with open(path, "rb") as f:
            b64 = base64.b64encode(f.read()).decode("ascii")
        uris.append(f"data:image/jpeg;base64,{b64}")
    return uris


def _oauth_fast_path():
    """Hands the browser a ready-made sign-in link for each provider, so pressing the Google or
    Microsoft button goes straight there instead of waiting for a full server round trip first.
    The links are good for two minutes; after 60 seconds the button just does it the slow way."""
    try:
        from streamlit.user_info import generate_login_redirect_url
        links = {}
        if _google_login_configured():
            links["google"] = generate_login_redirect_url("google")
        if _microsoft_login_configured():
            links["microsoft"] = generate_login_redirect_url("microsoft")
    except Exception:
        return
    if not links:
        return
    import json as _json
    st.html(
        "<script>(function(){"
        "window.__nxOauth = {links: " + _json.dumps(links) + ", t: Date.now()};"
        "if (window.__nxOauthHook) return; window.__nxOauthHook = true;"
        "document.addEventListener('click', function(e){"
        "var b = e.target && e.target.closest ? e.target.closest('[class*=\"st-key-auth_google_\"], [class*=\"st-key-auth_microsoft_\"]') : null;"
        "if (!b || !window.__nxOauth) return;"
        "var p = b.className.indexOf('auth_google_') > -1 ? 'google' : 'microsoft';"
        "var url = window.__nxOauth.links[p];"
        "if (!url || Date.now() - window.__nxOauth.t > 60000) return;"
        "e.preventDefault(); e.stopImmediatePropagation(); window.location.assign(url);"
        "}, true);"
        "})();</script>",
        unsafe_allow_javascript=True,
    )


def render_auth_page():
    """Full-screen sign-up/sign-in gate shown before the rest of the app.
    Single-account app: shows Sign Up if no account has ever been created,
    otherwise Sign In. Styling is scoped to this page only (most of it keys
    off .auth-page/.st-key-auth_form_panel), and the sidebar is hidden here
    since there's nothing to navigate to yet.
    """
    st.markdown(
        """
        <style>
        [data-testid="stSidebar"] { display: none; }
        [data-testid="stSidebarCollapsedControl"] { display: none; }

        /* Smooth arrival from the landing page: the two halves fade and glide
           in from opposite sides when they first mount. */
        @keyframes auth-glide-left {
            from { opacity: 0; transform: translateX(-28px) scale(0.985); }
            to   { opacity: 1; transform: none; }
        }
        @keyframes auth-glide-right {
            from { opacity: 0; transform: translateX(28px) scale(0.985); }
            to   { opacity: 1; transform: none; }
        }
        .st-key-auth_form_panel { animation: auth-glide-left 0.55s cubic-bezier(0.22, 1, 0.36, 1) both; }
        .auth-visual-panel { animation: auth-glide-right 0.7s cubic-bezier(0.22, 1, 0.36, 1) 0.05s both; }
        @media (prefers-reduced-motion: reduce) {
            .st-key-auth_form_panel, .auth-visual-panel { animation: none; }
        }

        .auth-title {
            color: #f8fafc;
            font-size: 1.9rem;
            font-weight: 700;
            letter-spacing: -0.01em;
            margin: 0 0 1.5rem 0;
        }

        /* The form column, turned into a real card via st.container(key=...) -
           a real wrapping element, unlike raw HTML split across markdown
           calls, which Streamlit would render as unnested siblings. */
        .st-key-auth_form_panel {
            background: linear-gradient(180deg, #161b22 0%, #11161d 100%);
            border: 1px solid #2c3340;
            border-radius: 20px;
            padding: 2.5rem 2.25rem;
        }

        .st-key-auth_submit button {
            background: linear-gradient(135deg, rgba(99,102,241,0.55), rgba(30,27,75,0.75))!important;
            border: 2px solid rgba(99,102,241,0.5)!important;
            color: #ffffff!important;
            font-weight: 700!important;
            padding: 0.9rem!important;
        }
        .st-key-auth_submit button p {
            color: #ffffff!important;
            font-weight: 700!important;
        }

        .st-key-auth_toggle button {
            background: transparent!important;
            border: none!important;
            color: #5aa2ff!important;
            text-decoration: underline;
        }

        /* Social sign-up/sign-in buttons. Google and Microsoft call real
           st.login(...) once configured - see _google_login_configured()
           and _microsoft_login_configured(). Icons are plain CSS background-images
           (data URIs) on a ::before pseudo-element rather than injected via
           JS, since any <script unsafe_allow_javascript> whose body contains
           a literal "<" - which full <svg> markup always does - gets
           silently dropped by Streamlit's sanitizer. */
        .st-key-auth_google_signup button, .st-key-auth_microsoft_signup button,
        .st-key-auth_google_login button, .st-key-auth_microsoft_login button {
            background: #ffffff!important;
            border: 1px solid #e2e2e2!important;
            position: relative!important;
            padding-left: 2.4rem!important;
        }
        .st-key-auth_google_signup button p, .st-key-auth_microsoft_signup button p,
        .st-key-auth_google_login button p, .st-key-auth_microsoft_login button p {
            color: #1a1a1a!important;
            font-weight: 600!important;
        }
        .st-key-auth_google_signup button::before, .st-key-auth_microsoft_signup button::before,
        .st-key-auth_google_login button::before, .st-key-auth_microsoft_login button::before {
            content: "";
            position: absolute;
            left: 1rem;
            top: 50%;
            transform: translateY(-50%);
            width: 18px;
            height: 18px;
            background-size: contain;
            background-repeat: no-repeat;
        }
        .st-key-auth_google_signup button::before, .st-key-auth_google_login button::before {
            background-image: url("data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIxOCIgaGVpZ2h0PSIxOCIgdmlld0JveD0iMCAwIDI0IDI0Ij48cGF0aCBkPSJNMjIuNTYgMTIuMjVjMC0uNzgtLjA3LTEuNTMtLjItMi4yNUgxMnY0LjI2aDUuOTJjLS4yNiAxLjM3LTEuMDQgMi41My0yLjIxIDMuMzF2Mi43N2gzLjU3YzIuMDgtMS45MiAzLjI4LTQuNzQgMy4yOC04LjA5WiIgZmlsbD0iIzQyODVGNCIvPjxwYXRoIGQ9Ik0xMiAyM2MyLjk3IDAgNS40Ni0uOTggNy4yOC0yLjY2bC0zLjU3LTIuNzdjLS45OC42Ni0yLjIzIDEuMDYtMy43MSAxLjA2LTIuODYgMC01LjI5LTEuOTMtNi4xNi00LjUzSDIuMTh2Mi44NEMzLjk5IDIwLjUzIDcuNyAyMyAxMiAyM1oiIGZpbGw9IiMzNEE4NTMiLz48cGF0aCBkPSJNNS44NCAxNC4xYy0uMjItLjY2LS4zNS0xLjM2LS4zNS0yLjFzLjEzLTEuNDQuMzUtMi4xVjcuMDZIMi4xOEMxLjQzIDguNTUgMSAxMC4yMiAxIDEycy40MyAzLjQ1IDEuMTggNC45NGwzLjY2LTIuODRaIiBmaWxsPSIjRkJCQzA1Ii8+PHBhdGggZD0iTTEyIDUuMzhjMS42MiAwIDMuMDYuNTYgNC4yMSAxLjY0bDMuMTUtMy4xNUMxNy40NSAyLjA5IDE0Ljk3IDEgMTIgMSA3LjcgMSAzLjk5IDMuNDcgMi4xOCA3LjA2bDMuNjYgMi44NEM2LjcxIDcuMyA5LjE0IDUuMzggMTIgNS4zOFoiIGZpbGw9IiNFQjQzMzUiLz48L3N2Zz4=");
        }
        .st-key-auth_microsoft_signup button::before, .st-key-auth_microsoft_login button::before {
            background-image: url("data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIxOCIgaGVpZ2h0PSIxOCIgdmlld0JveD0iMCAwIDIzIDIzIj48cGF0aCBmaWxsPSIjZjM1MzI1IiBkPSJNMSAxaDEwdjEwSDF6Ii8+PHBhdGggZmlsbD0iIzgxYmMwNiIgZD0iTTEyIDFoMTB2MTBIMTJ6Ii8+PHBhdGggZmlsbD0iIzA1YTZmMCIgZD0iTTEgMTJoMTB2MTBIMXoiLz48cGF0aCBmaWxsPSIjZmZiYTA4IiBkPSJNMTIgMTJoMTB2MTBIMTJ6Ii8+PC9zdmc+");
        }

        .auth-or-divider {
            display: flex;
            align-items: center;
            gap: 1rem;
            color: rgba(255,255,255,0.35);
            font-size: 0.8rem;
            margin: 1.25rem 0;
        }
        .auth-or-divider .line {
            flex: 1;
            height: 1px;
            background: rgba(255,255,255,0.12);
        }

        /* Right panel: dark gradient + the image corridor + tagline text. */
        .auth-visual-panel {
            position: relative;
            min-height: 640px;
            border-radius: 20px;
            overflow: hidden;
            background: linear-gradient(170deg, #000000 0%, #161b22 55%, #0e1117 100%);
            padding: 3rem 2.5rem;
        }
        /* Same blue radial glow as the Home hero (.home-hero-glow) - identical
           color and falloff - centered on the corridor's vanishing point and
           layered behind the moving cards (it precedes them in the DOM). */
        .auth-visual-glow {
            position: absolute;
            top: 55%;
            left: 50%;
            width: 680px;
            height: 460px;
            transform: translate(-50%, -50%);
            background: radial-gradient(closest-side, rgba(90, 162, 255, 0.4), rgba(90, 162, 255, 0));
            pointer-events: none;
            z-index: 0;
        }
        .corridor-stage { position: absolute; inset: 0; pointer-events: none; }
        .corridor-space { position: absolute; inset: 0; transform-style: preserve-3d; }
        .corridor-card { position: absolute; overflow: hidden; box-shadow: 0 10px 30px rgba(0,0,0,0.4); }
        .corridor-card img { width: 100%; height: 100%; object-fit: cover; display: block; }

        .auth-tagline { position: relative; z-index: 2; max-width: 420px; }
        .auth-tagline-title {
            color: #f8fafc;
            font-size: 2.1rem;
            font-weight: 700;
            line-height: 1.15;
            letter-spacing: -0.02em;
            margin: 0 0 0.9rem 0;
        }
        .auth-tagline-sub {
            color: rgba(255,255,255,0.65);
            font-size: 0.95rem;
            line-height: 1.5;
            margin: 0;
        }

        @media (prefers-reduced-motion: reduce) {
            .corridor-card { animation-play-state: paused !important; }
        }
        </style>
        """,
        unsafe_allow_html=True,
    )

    existing_user = load_user()
    # Which form to show is chosen on the landing page (Log in / Sign up);
    # fall back to the old rule if this page was reached some other way.
    mode = st.session_state.get("auth_view") or ("login" if existing_user else "signup")

    left, right = st.columns([0.94, 1.06], gap="large")

    with right:
        images = _load_auth_corridor_images()
        st.markdown(
            "<div class='auth-visual-panel'>"
            "<div class='auth-tagline'>"
            "<p class='auth-tagline-title'>Your notes,<br/>made easy to master.</p>"
            "<p class='auth-tagline-sub'>Upload a PDF and get flashcards, quizzes, and progress "
            "tracking built for how you actually study.</p>"
            "</div>"
            "<div class='auth-visual-glow'></div>"
            + render_image_corridor(images, container_id="auth")
            + "</div>",
            unsafe_allow_html=True,
        )
        _oauth_fast_path()

    with left:
        with st.container(key="auth_form_panel"):
            google_ready = _google_login_configured()

            if st.button("← Back to home", key="auth_back"):
                st.session_state.show_auth = False
                st.rerun()

            if mode == "signup":
                st.markdown("<p class='auth-title'>Create an account</p>", unsafe_allow_html=True)

                col_google, col_apple = st.columns(2)
                with col_google:
                    if st.button("Sign up with Google", key="auth_google_signup", use_container_width=True):
                        if google_ready:
                            st.login("google")
                        else:
                            st.info("Google sign-in isn't set up yet - use the form below for now.")
                with col_apple:
                    if st.button("Sign up with Microsoft", key="auth_microsoft_signup", use_container_width=True):
                        if _microsoft_login_configured():
                            st.login("microsoft")
                        else:
                            st.info("Microsoft sign-in isn't set up yet - use Google or the form below for now.")
                st.markdown(
                    "<div class='auth-or-divider'><div class='line'></div>or<div class='line'></div></div>",
                    unsafe_allow_html=True,
                )

                with st.form("auth_signup_form"):
                    col_fn, col_ln = st.columns(2)
                    with col_fn:
                        first_name = st.text_input("First name", placeholder="e.g. Morikeh")
                    with col_ln:
                        last_name = st.text_input("Last name", placeholder="e.g. Kaba")
                    email = st.text_input("Email", placeholder="you@example.com")
                    password = st.text_input("Password", type="password", placeholder="Create a password")
                    confirm = st.text_input("Confirm password", type="password", placeholder="Re-enter your password")
                    submitted = st.form_submit_button(
                        "🔐  Create Account", key="auth_submit", use_container_width=True
                    )

                if submitted:
                    errors = []
                    if not first_name.strip() or not last_name.strip():
                        errors.append("Enter your first and last name.")
                    if not email.strip() or "@" not in email:
                        errors.append("Enter a valid email address.")
                    if len(password) < 8:
                        errors.append("Password must be at least 8 characters.")
                    if password != confirm:
                        errors.append("Passwords don't match.")
                    if not errors and existing_user:
                        # One local account only - never overwrite it from here.
                        errors.append("An account already exists on this device. Please log in instead.")
                    if errors:
                        for e in errors:
                            st.error(e)
                    else:
                        create_user(first_name, last_name, email, password)
                        st.session_state.authenticated = True
                        st.session_state.settings["display_name"] = f"{first_name.strip()} {last_name.strip()}".strip()
                        save_settings(st.session_state.settings)
                        st.rerun()

                if st.button("Already have an account? Log in", key="auth_switch_login", use_container_width=True):
                    st.session_state.auth_view = "login"
                    st.rerun()
            else:
                st.markdown("<p class='auth-title'>Welcome back</p>", unsafe_allow_html=True)

                col_google, col_apple = st.columns(2)
                with col_google:
                    if st.button("Sign in with Google", key="auth_google_login", use_container_width=True):
                        if google_ready:
                            st.login("google")
                        else:
                            st.info("Google sign-in isn't set up yet - use the form below for now.")
                with col_apple:
                    if st.button("Sign in with Microsoft", key="auth_microsoft_login", use_container_width=True):
                        if _microsoft_login_configured():
                            st.login("microsoft")
                        else:
                            st.info("Microsoft sign-in isn't set up yet - use Google or the form below for now.")
                st.markdown(
                    "<div class='auth-or-divider'><div class='line'></div>or<div class='line'></div></div>",
                    unsafe_allow_html=True,
                )

                with st.form("auth_login_form"):
                    email = st.text_input("Email", placeholder="you@example.com")
                    password = st.text_input("Password", type="password", placeholder="Enter your password")
                    submitted = st.form_submit_button(
                        "🔐  Sign In", key="auth_submit", use_container_width=True
                    )

                if submitted:
                    if verify_user(email, password):
                        st.session_state.authenticated = True
                        st.rerun()
                    elif not existing_user:
                        st.error("No account exists yet - sign up first.")
                    else:
                        st.error("Incorrect email or password.")

                if st.button("New here? Sign up", key="auth_switch_signup", use_container_width=True):
                    st.session_state.auth_view = "signup"
                    st.rerun()


# ---- Study time -----------------------------------------------------------
# Like the streak, real elapsed time is tracked from scratch rather than
# guessed from quiz counts, so it starts at 0 and only ever grows from real
# use going forward.
STUDY_TIME_JSON = os.path.join(DATA_DIR, "study_time.json")
STUDY_HEARTBEAT_CAP_SECONDS = 20 * 60  # a gap longer than this isn't counted


def load_study_time() -> dict:
    if not _persisting():
        return {}
    if os.path.exists(STUDY_TIME_JSON):
        try:
            with open(STUDY_TIME_JSON, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                return data
        except (json.JSONDecodeError, OSError):
            pass
    return {}


def save_study_time(data: dict):
    if not _persisting():
        return
    temp_path = STUDY_TIME_JSON + ".tmp"
    with open(temp_path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
    os.replace(temp_path, STUDY_TIME_JSON)


def record_study_heartbeat():
    """Add real elapsed time to today's study-time total while a note is open.

    Streamlit only runs code in response to an action, so there's no running
    clock to read. This approximates one from the gap between reruns (opening
    a card, submitting an answer, etc.) instead. A gap longer than the cap -
    the tab sitting idle or in the background - isn't counted, so leaving the
    app open overnight can't inflate the total.
    """
    now = time.time()
    last = st.session_state.get("study_heartbeat_ts")
    st.session_state["study_heartbeat_ts"] = now
    if last is None:
        return
    elapsed = now - last
    if elapsed <= 0 or elapsed > STUDY_HEARTBEAT_CAP_SECONDS:
        return
    today_iso = date.today().isoformat()
    data = load_study_time()
    data[today_iso] = data.get(today_iso, 0) + elapsed
    save_study_time(data)


def format_study_duration(total_seconds: float) -> str:
    hours = total_seconds / 3600
    if hours >= 1:
        return f"{hours:.1f} hrs"
    minutes = total_seconds / 60
    if minutes >= 1:
        return f"{minutes:.0f} min"
    return "Just started"


# ---- Home page data helpers ------------------------------------------------
_MONTH_ABBR = {
    1: "Jan.", 2: "Feb.", 3: "Mar.", 4: "Apr.", 5: "May", 6: "June", 7: "July",
    8: "Aug.", 9: "Sept.", 10: "Oct.", 11: "Nov.", 12: "Dec.",
}


def format_relative_study_date(d: date, today=None) -> str:
    today = today or date.today()
    if d == today:
        return "Studied today"
    if d == today - timedelta(days=1):
        return "Yesterday"
    label = f"{_MONTH_ABBR[d.month]} {d.day}"
    if d.year != today.year:
        label += f", {d.year}"
    return label


def compute_overview_stats(notes: dict) -> dict:
    """Real, disk-backed totals shared by the Home page and the Study Mode stats bar."""
    all_percentages = [
        attempt.get("percentage", 0)
        for note in notes.values()
        for attempt in note.get("quiz_history", [])
    ]
    return {
        "total_notes": len(notes),
        "total_quizzes": len(all_percentages),
        "avg_score": round(sum(all_percentages) / len(all_percentages), 1) if all_percentages else 0,
    }


def get_last_touched_at(note: dict):
    """The most recent moment this note was really studied, as a full
    timestamp: its latest quiz attempt, or when it was uploaded if it has
    never been quizzed. Full precision (not just the day) matters for sorting
    same-day notes into the right order."""
    quiz_timestamps = []
    for attempt in note.get("quiz_history", []):
        raw = attempt.get("date")
        if isinstance(raw, str):
            try:
                quiz_timestamps.append(datetime.fromisoformat(raw))
            except ValueError:
                pass
    if quiz_timestamps:
        return max(quiz_timestamps)
    created_at = note.get("created_at")
    if created_at:
        try:
            return datetime.strptime(created_at, "%Y-%m-%d %I:%M %p")
        except ValueError:
            return None
    return None


def get_last_touched_date(note: dict):
    """Just the day from get_last_touched_at(), for callers that only need that."""
    touched_at = get_last_touched_at(note)
    return touched_at.date() if touched_at else None


def get_recent_notes(notes: dict, limit: int = 3):
    """[(note_id, note, last_touched_date), ...], most recently studied first."""
    dated = [(get_last_touched_at(note), note_id, note) for note_id, note in notes.items()]
    dated = [(touched_at, note_id, note) for touched_at, note_id, note in dated if touched_at]
    dated.sort(key=lambda row: row[0], reverse=True)
    return [(note_id, note, touched_at.date()) for touched_at, note_id, note in dated[:limit]]


def get_continue_note(notes: dict):
    """The note to resume: whichever was studied (or uploaded) most recently."""
    recent = get_recent_notes(notes, limit=1)
    if not recent:
        return None
    note_id, note, _ = recent[0]
    return {"id": note_id, "title": note.get("title", "Untitled")}


def find_recommendation(notes: dict):
    """The most recent quiz attempt that wasn't a perfect score, across all notes,
    for the Home page's "Recommended Next Step" card. None if there isn't one."""
    attempts = [
        (attempt.get("date", ""), note_id, note, attempt)
        for note_id, note in notes.items()
        for attempt in note.get("quiz_history", [])
    ]
    attempts.sort(key=lambda row: row[0], reverse=True)  # ISO timestamps sort chronologically
    for _, note_id, note, attempt in attempts:
        if attempt.get("percentage", 100) < 100:
            return note_id, note, attempt
    return None


def start_quiz_retake(note_id: str, note: dict):
    """Session state for jumping straight into a fresh attempt of a note's quiz
    (used by the Home page's "Study Again" button)."""
    if not note.get("quiz"):
        return
    st.session_state[f"quiz_started_{note_id}"] = True
    st.session_state[f"quiz_current_{note_id}"] = 0
    st.session_state[f"quiz_score_{note_id}"] = 0
    st.session_state[f"quiz_answers_{note_id}"] = {}
    st.session_state[f"quiz_submitted_{note_id}"] = False
    st.session_state[f"quiz_results_saved_{note_id}"] = False
    st.session_state[f"active_study_tab_{note_id}"] = "🎯 Quiz"


def extract_text_from_pdf(uploaded_file):
    """Extract text from uploaded PDF.

    Uses pypdfium2 (Chromium's own PDF engine) rather than pypdf: pypdf
    reconstructs spacing purely from raw character x-gaps, which on
    justified/kerned text produces words glued together with no space at
    all ("Ihaveseenaweasel") interspersed with spurious spaces inside
    other words ("s it t in g"). pdfium's layout-aware extraction gets word
    boundaries right on the same text almost all of the time.
    """
    try:
        pdf = pdfium.PdfDocument(uploaded_file.getvalue())
        try:
            text = ""
            for page in pdf:
                textpage = page.get_textpage()
                try:
                    text += textpage.get_text_range() + "\n"
                finally:
                    textpage.close()
        finally:
            pdf.close()
        # U+FFFE/U+FFFF are Unicode noncharacters, never valid text - some PDFs'
        # embedded fonts map a broken discretionary-hyphenation glyph to one of
        # these, which would otherwise show up as a stray replacement box.
        text = text.replace("￾", "").replace("￿", "")
        return clean_extracted_text(text)
    except Exception as e:
        st.error(f"Error extracting text from PDF: {str(e)}")
        return "Error: Could not extract text from this PDF. Please try a different file."


@st.cache_data(show_spinner=False)
def _pdf_page_count(pdf_path: str, mtime: float) -> int:
    import pypdfium2 as pdfium
    pdf = pdfium.PdfDocument(pdf_path)
    try:
        return len(pdf)
    finally:
        pdf.close()


@st.cache_data(show_spinner=False, max_entries=96)
def _render_pdf_page(pdf_path: str, mtime: float, page_index: int, width_px: int) -> bytes:
    """Render one PDF page at exactly `width_px` pixels wide, as image bytes.

    Drawing the page at the exact size it will be shown at (instead of
    shrinking a bigger picture in the browser) keeps text edges crisp. Lossless
    PNG is used so compression doesn't smear the text; very busy pages (e.g.
    scans) where PNG gets huge fall back to near-lossless JPEG (q95, no chroma
    subsampling).
    """
    import io
    import pypdfium2 as pdfium
    pdf = pdfium.PdfDocument(pdf_path)
    try:
        page = pdf[page_index]
        # pdfium rounds the bitmap size up, so aim a hair under to land on width_px exactly.
        image = page.render(scale=(width_px - 0.01) / page.get_width()).to_pil().convert("RGB")
    finally:
        pdf.close()
    buffer = io.BytesIO()
    image.save(buffer, format="PNG")
    if buffer.tell() > 1_500_000:
        buffer = io.BytesIO()
        image.save(buffer, format="JPEG", quality=95, subsampling=0)
    return buffer.getvalue()


def _page_image_html(pdf_path: str, mtime: float, page_index: int, zoom: str) -> str:
    """HTML for one page image that is pixel-sharp on any screen scaling.

    The page is drawn at several exact pixel sizes and a tiny script shows the
    one that maps 1:1 onto the screen's pixels (on-screen CSS size times the
    screen's pixel density), so the browser never has to stretch or resample
    it. That resampling, plus st.image() shrinking the picture on the server
    and re-saving it as a JPEG, is what made the text blurry.
    """
    import base64
    import io
    import json
    import uuid
    from PIL import Image

    fit_page = zoom == "Fit page"
    if fit_page:
        # The displayed size depends on the window, so offer a ladder of sizes.
        widths = [300, 375, 470, 590, 730, 910, 1140, 1420, 1780, 2200]
        target_css_width = 0
    else:
        target_css_width = PREVIEW_ZOOM_WIDTHS[zoom]
        widths = [round(target_css_width * density) for density in (1, 1.25, 1.5, 1.75, 2, 2.5, 3)]

    ladder = []  # [width, height, data URI] for each size
    for width in widths:
        data = _render_pdf_page(pdf_path, mtime, page_index, width)
        mime = "image/png" if data[:4] == b"\x89PNG" else "image/jpeg"
        with Image.open(io.BytesIO(data)) as rendered:
            height = rendered.height
        ladder.append([width, height, f"data:{mime};base64,{base64.b64encode(data).decode('ascii')}"])

    if fit_page:
        aspect = ladder[0][0] / ladder[0][1]
        size_css = (
            f"height:calc(100vh - 290px);width:auto;aspect-ratio:{aspect:.4f};"
            "max-width:100%;object-fit:contain;"
        )
    else:
        size_css = f"width:{target_css_width}px;max-width:100%;height:auto;object-fit:contain;"

    element_id = f"docpage-{uuid.uuid4().hex[:10]}"
    # Fixed sizes: show the smallest render at least as big as the on-screen size
    # in device pixels (or the biggest that fits, if the pop-up is narrower).
    # "Fit page": show the biggest render that fits the window. Either way the
    # render is sized in exact device pixels with smoothing off, so it maps 1:1
    # onto the screen and the text is pixel-identical to the render.
    # Note: no "<" in the script, Streamlit's HTML sanitizer drops scripts
    # containing it.
    script = (
        "<script>(function(){"
        f"var img=document.getElementById('{element_id}');if(!img)return;"
        f"var ladder={json.dumps(ladder)};var target={target_css_width};"
        "var base=img.getAttribute('style');"
        "function apply(){"
        "if(!img.isConnected){window.removeEventListener('resize',apply);return;}"
        "var dpr=window.devicePixelRatio;var availW=img.parentElement.clientWidth*dpr;"
        "var best=ladder[0];"
        "if(target){"
        "var need=target*dpr;"
        "for(var i=0;ladder.length>i;i++){if(availW+1>=ladder[i][0]){best=ladder[i];if(ladder[i][0]>=need-1){break;}}}"
        "}else{"
        "var availH=(window.innerHeight-290)*dpr;"
        "for(var j=0;ladder.length>j;j++){if(availH>=ladder[j][1]&&availW>=ladder[j][0]){best=ladder[j];}}"
        "}"
        "if(img.getAttribute('data-w')!==String(best[0])){img.setAttribute('data-w',best[0]);img.src=best[2];}"
        "var style=base+';width:'+(best[0]/dpr)+'px;height:'+(best[1]/dpr)+'px;image-rendering:pixelated';"
        "if(img.getAttribute('style')!==style){img.setAttribute('style',style);}"
        "}"
        "apply();window.addEventListener('resize',apply);"
        "})();</script>"
    )
    return (
        "<div style='text-align:center'>"
        f"<img id='{element_id}' src='{ladder[0][2]}' alt='Document page' "
        f"style='display:inline-block;{size_css}'>"
        "</div>" + script
    )

# Displayed page width (in pixels) for the fixed zoom levels. "Fit page" is
# sized to the window height with CSS instead.
PREVIEW_ZOOM_WIDTHS = {"Standard": 640, "Large": 900}


def _upload_dropzone_script(max_mb) -> str:
    """Turns the real file uploader into a big drag-and-drop card, without
    changing how uploads actually work.

    The installed Streamlit version renders the uploader as just a small
    "Upload" button plus a size/type caption - not the classic big dropzone.
    This hides those two native pieces (via CSS) and adds a custom-styled
    replacement into the same section. The section itself, and the real
    (still-present, just hidden) button and file input inside it, are left
    completely alone, so drag-and-drop dropped there still works, and the
    custom "Browse Files" button just forwards its click to the real one.

    Note: no "<" anywhere in the script body - Streamlit's HTML sanitizer
    silently drops any script containing one.
    """
    nonce = uuid.uuid4().hex  # makes the body differ each rerun, so the effect always re-fires
    return (
        "<script>(function(){"
        f"var _nonce='{nonce}';"
        "function makeEl(tag,cls,text){"
        "var el=document.createElement(tag);"
        "if(cls)el.className=cls;"
        "if(text!==undefined)el.textContent=text;"
        "return el;"
        "}"
        "function cloudIcon(){"
        "var ns='http://www.w3.org/2000/svg';"
        "var s=document.createElementNS(ns,'svg');"
        "s.setAttribute('viewBox','0 0 24 24');s.setAttribute('fill','none');s.setAttribute('stroke','currentColor');"
        "s.setAttribute('stroke-width','1.5');s.setAttribute('stroke-linecap','round');s.setAttribute('stroke-linejoin','round');"
        "s.setAttribute('class','upload-dropzone-cloud');"
        "['M4 14.899A7 7 0 1 1 15.71 8h1.79a4.5 4.5 0 0 1 2.5 8.242','M12 12v9','m16 16-4-4-4 4'].forEach(function(d){"
        "var p=document.createElementNS(ns,'path');p.setAttribute('d',d);s.appendChild(p);});"
        "return s;"
        "}"
        "function customize(){"
        "var sections=document.querySelectorAll(\"[data-testid='stFileUploaderDropzone']\");"
        "for(var i=0;sections.length>i;i++){"
        "var section=sections[i];"
        "if(section.dataset.customized==='true')continue;"
        "var nativeButton=section.querySelector('button');"
        "if(!nativeButton)continue;"
        "section.dataset.customized='true';"
        "var overlay=makeEl('div','upload-dropzone-overlay');"
        "var iconWrap=makeEl('div','upload-dropzone-icon');"
        "iconWrap.appendChild(cloudIcon());"
        "overlay.appendChild(iconWrap);"
        "overlay.appendChild(makeEl('div','upload-dropzone-headline','Upload your PDF'));"
        "var sub=makeEl('div','upload-dropzone-sub','Drag & drop your PDF here, or ');"
        "sub.appendChild(makeEl('span','upload-dropzone-browse-link','browse'));"
        "overlay.appendChild(sub);"
        f"overlay.appendChild(makeEl('div','upload-dropzone-caption','PDF \u2022 Maximum {int(max_mb)} MB'));"
        "section.appendChild(overlay);"
        "overlay.addEventListener('click',function(e){e.stopPropagation();nativeButton.click();});"
        "['dragenter','dragover'].forEach(function(t){section.addEventListener(t,function(){section.classList.add('is-dragging');});});"
        "['dragleave','drop'].forEach(function(t){section.addEventListener(t,function(){section.classList.remove('is-dragging');});});"
        "}"
        "}"
        "customize();"
        "if(window.__uploadDropzoneObserver)window.__uploadDropzoneObserver.disconnect();"
        "window.__uploadDropzoneObserver=new MutationObserver(customize);"
        "window.__uploadDropzoneObserver.observe(document.body,{childList:true,subtree:true});"
        "})();</script>"
    )


def _instant_save_overlay_script() -> str:
    """Shows a loading line the instant Save Notes is clicked, with no
    server round-trip, right below the button - the exact spot the real
    st.spinner() shows up once it arrives.

    Saving can take over a second (extracting a PDF's text isn't instant),
    and it turns out Streamlit doesn't flush its own st.spinner() to the
    browser until that work yields control back - so even the "real" spinner
    can visibly lag behind the click by up to a second. This reacts to the
    actual browser click event directly, so the loading state appears the
    moment the button is pressed. It hands off to the real spinner once that
    arrives (or the save finishes, or an error shows), and a timeout is a
    last-resort safety net so it can never get stuck showing forever.

    Note: no "<" anywhere in the script body - Streamlit's HTML sanitizer
    silently drops any script containing one.
    """
    nonce = uuid.uuid4().hex  # makes the body differ each rerun, so the effect always re-fires
    return (
        "<script>(function(){"
        f"var _nonce='{nonce}';"
        "var btn=document.querySelector('.st-key-save_notes_btn button');"
        "if(!btn||btn.dataset.instantSaveBound==='true')return;"
        "btn.dataset.instantSaveBound='true';"
        "btn.addEventListener('click',function(){"
        "if(document.getElementById('instant-save-overlay'))return;"
        "var anchor=btn.closest('.st-key-save_notes_btn');"
        "if(!anchor)return;"
        "var el=document.createElement('div');"
        "el.id='instant-save-overlay';"
        "el.className='instant-save-overlay';"
        "var spin=document.createElement('span');"
        "spin.className='instant-save-spin';"
        "var txt=document.createElement('span');"
        "txt.textContent='Saving your notes...';"
        "el.appendChild(spin);"
        "el.appendChild(txt);"
        # Placed as a sibling right after the button's own container - the
        # same spot in the page flow the real spinner renders into - not a
        # floating banner elsewhere, so there's only ever one loading
        # indicator, in one place, the whole time.
        "anchor.insertAdjacentElement('afterend',el);"
        "var start=Date.now();"
        "var iv=setInterval(function(){"
        "var stillThere=document.querySelector('.st-key-save_notes_btn button');"
        "var realSpinner=document.querySelector(\"[data-testid='stSpinner']\");"
        "var spinnerUp=realSpinner&&realSpinner.offsetParent!==null;"
        "var err=document.querySelector(\"[data-testid='stException']\");"
        "var timedOut=Date.now()-start>30000;"
        "if(!stillThere||spinnerUp||err||timedOut){"
        "el.remove();"
        "clearInterval(iv);"
        "}"
        "},100);"
        "});"
        "})();</script>"
    )


def show_document_preview(title: str, pdf_path: str):
    """Pop-up viewer showing the original uploaded PDF for a note.

    Renders pages as images at a controlled, document-like size (rather than
    stretching to the window width), with a zoom control and page picker. This
    works for every PDF without depending on a browser plugin or a Streamlit
    component that has to be registered at server startup.
    """

    # Defined per call so the note's title can be the pop-up's own title
    # instead of costing an extra row of vertical space inside it.
    @st.dialog(f"📄 {title}", width="large")
    def _preview_dialog():
        if not pdf_path or not os.path.exists(pdf_path):
            st.warning("The original PDF file for this note couldn't be found.")
            return

        try:
            mtime = os.path.getmtime(pdf_path)
            total_pages = _pdf_page_count(pdf_path, mtime)
            if total_pages < 1:
                raise ValueError("PDF has no pages")

            zoom_col, page_col = st.columns([3, 2])
            with zoom_col:
                zoom = st.segmented_control(
                    "Size",
                    options=["Fit page", "Standard", "Large"],
                    default="Standard",
                    key="preview_zoom",
                    label_visibility="collapsed",
                ) or "Standard"
            with page_col:
                if total_pages > 1:
                    page_number = st.number_input(
                        f"Page (1 - {total_pages})",
                        min_value=1,
                        max_value=total_pages,
                        value=1,
                        step=1,
                        key=f"preview_page_{pdf_path}",
                        label_visibility="collapsed",
                    )
                else:
                    page_number = 1

            st.html(
                _page_image_html(pdf_path, mtime, int(page_number) - 1, zoom),
                unsafe_allow_javascript=True,
            )
            if total_pages > 1:
                st.caption(f"Page {int(page_number)} of {total_pages}")
        except Exception:
            st.error("This document couldn't be displayed. The PDF file may be damaged.")

    _preview_dialog()


# ===============================
# 4. Load notes ONCE (VERY IMPORTANT)
# ===============================
# Streamlit's own OAuth session (set after a successful st.login("google")
# round trip) counts as signed in. Checked before any data is loaded so a
# Google sign-in gets the saved data, not a guest's empty state.
try:
    # "signed_out" stops the still-present Google identity from signing the
    # user straight back in during the moment between pressing Sign Out and
    # Streamlit's logout redirect finishing; after that the cookie is gone,
    # so a reload stays in guest mode until they choose to log in again.
    if (st.user.is_logged_in and not st.session_state.get("authenticated")
            and not st.session_state.get("signed_out")):
        st.session_state.authenticated = True
except AttributeError:
    pass  # auth not configured at all yet - st.user has no attributes

# Guests start from empty, in-memory state and never see (or write) the saved
# data. It's (re)loaded whenever the signed-in/guest mode changes: signing in
# loads the saved data from disk, signing out drops back to a clean guest.
_signed_in = bool(st.session_state.get("authenticated"))
if st.session_state.get("data_mode") != _signed_in:
    st.session_state.data_mode = _signed_in
    if _signed_in:
        st.session_state.notes = load_notes()
        st.session_state.streak_data = load_streak()
        st.session_state.settings = load_settings()
    else:
        st.session_state.notes = {}
        st.session_state.streak_data = {"study_dates": []}
        st.session_state.settings = copy.deepcopy(SETTINGS_DEFAULTS)
    # Per-note UI state (selected note, quiz progress, ...) belongs to the
    # previous mode's notes and would point at notes that no longer exist.
    for _key in list(st.session_state.keys()):
        if _key.startswith(("study_mode_note_select", "quiz_", "active_study_tab_",
                            "flashcard", "fc_", "rename_input_", "preview_", "study_heartbeat_ts",
                            "last_uploaded_file_id", "last_saved_upload", "note_title_input")):
            del st.session_state[_key]

# ===============================
# 5. Page config + styling
# ===============================
# The browser tab shows the NexLearn mark, and the title follows the page like
# Gmail's tab does: "Upload Notes - NexLearn", "Settings - NexLearn", ... The
# page is known here already (the sidebar radio's value is in session_state
# before the script runs), so no script is needed to rename the tab.
if st.session_state.get("authenticated"):
    _tab_page = st.session_state.get("pending_page") or st.session_state.get("page") or "Home"
    _tab_title = f"{_tab_page} - NexLearn"
elif st.session_state.get("show_auth"):
    _tab_title = ("Log in" if st.session_state.get("auth_view") == "login" else "Sign up") + " - NexLearn"
else:
    _tab_title = "NexLearn"
def _paint_boot_background():
    """Streamlit's own page shell has no background colour, so on a reload the browser shows a white
    blank until Streamlit's scripts start (the white-then-black flash). This adds one small <style> and
    <script> to that shell: the window is dark (or, for someone using the Light theme, light) from the
    first frame (and Streamlit's own white app frame, which shows for a moment before the app's styles
    arrive). Safe to run every time - it only writes once - and a Streamlit reinstall is healed
    the next time the app runs."""
    try:
        import os as _os
        index_path = _os.path.join(_os.path.dirname(st.__file__), "static", "index.html")
        with open(index_path, "r", encoding="utf-8") as fh:
            page = fh.read()
        if "nx-boot-v3" in page:
            return
        import re as _re
        page = _re.sub(r'<style id="nx-boot[^"]*">.*?</script>', "", page, flags=_re.S)  # an older version of this, if any
        boot = (
            '<style id="nx-boot-v3">html,html body,.stApp{background:#0e1117 !important}'
            'html.nx-boot-light,html.nx-boot-light body,html.nx-boot-light .stApp{background:#f7faff !important}</style>'
            '<script>try{if(localStorage.getItem("nx-theme")==="light")document.documentElement.classList.add("nx-boot-light")}catch(e){}</script>'
        )
        page = page.replace("<head>", "<head>" + boot, 1)
        with open(index_path, "w", encoding="utf-8") as fh:
            fh.write(page)
    except Exception:
        pass  # purely cosmetic - never let it stop the app


_paint_boot_background()

st.set_page_config(
    page_title=_tab_title,
    page_icon=os.path.join("static", "nexlearn_favicon.png"),
    layout="wide"
)

st.markdown("""
<style>
.stApp {
    background-color: #0e1117;
    color: white;
}

/* the top bar never paints a white strip over the dark pages (e.g. while moving to the sign-in page) */
[data-testid="stHeader"] { background: transparent !important; }

/* Striped button styling */
.striped-button {
    background: linear-gradient(90deg, white 0%, white 50%, #4a90e2 50%, #4a90e2 100%);
    background-size: 20px 100%;
    background-position: 0 0;
    color: #0e1117;
    border: 2px solid #4a90e2;
    padding: 10px 24px;
    border-radius: 4px;
    font-weight: bold;
    cursor: pointer;
    transition: all 0.3s ease;
}

.striped-button:hover {
    background-position: -10px 0;
    transform: scale(1.02);
}

/* Default (secondary) Streamlit buttons render a white background;
   without this the inherited white app text is invisible on them. */
button[data-testid="stBaseButton-secondary"] p {
    color: #4a4a4a;
}

.quiz-shell {
    max-width: 760px;
    margin: 0 auto;
}

.quiz-question-card {
    background: linear-gradient(180deg, #161b22 0%, #11161d 100%);
    border: 1px solid #2c3340;
    border-radius: 20px;
    padding: 1.5rem;
    margin: 0.75rem 0 1rem 0;
    box-shadow: 0 14px 30px rgba(0, 0, 0, 0.18);
}

.quiz-progress-label {
    color: #94a3b8;
    font-size: 0.92rem;
    margin-bottom: 0.35rem;
}

.quiz-question-text {
    color: #f8fafc;
    font-size: 1.35rem;
    line-height: 1.45;
    font-weight: 700;
    margin: 0;
}

.quiz-section-label {
    color: #cbd5e1;
    font-size: 0.95rem;
    font-weight: 600;
    margin: 0.85rem 0 0.65rem 0;
}

.quiz-option-card {
    display: flex;
    gap: 0.9rem;
    align-items: flex-start;
    border-radius: 16px;
    border: 1px solid #2f3848;
    background: #141922;
    padding: 0.95rem 1rem;
    margin-bottom: 0.75rem;
}

.quiz-option-badge {
    width: 2rem;
    height: 2rem;
    border-radius: 999px;
    background: #243041;
    color: #f8fafc;
    display: flex;
    align-items: center;
    justify-content: center;
    font-weight: 700;
    flex-shrink: 0;
}

.quiz-option-text {
    color: #eef2ff;
    line-height: 1.55;
    font-size: 1rem;
}

.quiz-option-correct {
    border-color: #1f8f5f;
    background: rgba(23, 92, 61, 0.28);
}

.quiz-option-correct .quiz-option-badge {
    background: #1f8f5f;
}

.quiz-option-incorrect {
    border-color: #b54a4a;
    background: rgba(122, 37, 37, 0.26);
}

.quiz-option-incorrect .quiz-option-badge {
    background: #b54a4a;
}

.quiz-explanation-card {
    border: 1px solid #314056;
    background: #121a25;
    border-radius: 18px;
    padding: 1rem 1.1rem;
    margin-top: 1rem;
}

.quiz-explanation-title {
    color: #f8fafc;
    font-size: 1rem;
    font-weight: 700;
    margin-bottom: 0.45rem;
}

.quiz-explanation-body {
    color: #dbe4f0;
    line-height: 1.6;
}

div[data-testid="stRadio"] > label {
    display: none;
}

div[data-testid="stRadio"] div[role="radiogroup"] {
    gap: 0.8rem;
}

div[data-testid="stRadio"] div[role="radiogroup"] label {
    border: 1px solid #2f3848;
    border-radius: 16px;
    padding: 0.95rem 1rem;
    background: #141922;
    align-items: flex-start;
    gap: 0.85rem;
    transition: border-color 0.18s ease, background 0.18s ease, transform 0.18s ease;
}

div[data-testid="stRadio"] div[role="radiogroup"] label:hover {
    border-color: #5aa2ff;
    background: #172131;
    transform: translateY(-1px);
}

div[data-testid="stRadio"] div[role="radiogroup"] label p {
    color: #eef2ff;
    font-size: 1rem;
    line-height: 1.55;
}

div[data-testid="stRadio"] div[role="radiogroup"] label > div:first-child {
    margin-top: 0.2rem;
}

div[data-testid="stRadio"] div[role="radiogroup"] label:has(input:checked) {
    border-color: #5aa2ff;
    background: #18283d;
    box-shadow: 0 0 0 1px rgba(90, 162, 255, 0.28);
}

div[data-testid="stRadio"] div[role="radiogroup"] label:has(input:checked) p {
    color: #ffffff;
}

div[data-testid="stRadio"] div[role="radiogroup"] label > div:first-child [data-testid="stMarkdownContainer"] {
    display: none;
}

/* Shared page header (Upload Notes, and anywhere else that wants the same look) */
.page-title {
    color: #f8fafc;
    font-size: 1.4rem;
    font-weight: 700;
    margin: 0;
}

.app-subtitle {
    color: #94a3b8;
    margin: 0.15rem 0 1rem 0;
}

/* Home page */
/* Decorative glow behind the hero area - pure CSS (no external image), sits
   behind everything and never intercepts clicks. */
.home-hero-wrap {
    position: relative;
}

.home-hero-glow {
    position: absolute;
    top: -160px;
    left: 30%;
    width: 560px;
    height: 360px;
    transform: translateX(-50%);
    background: radial-gradient(closest-side, rgba(90, 162, 255, 0.4), rgba(90, 162, 255, 0));
    pointer-events: none;
    z-index: 0;
}

.home-badge {
    position: relative;
    z-index: 1;
    display: inline-flex;
    align-items: center;
    gap: 0.45rem;
    padding: 0.4rem 0.9rem;
    border-radius: 999px;
    border: 1px solid #2f3848;
    background: rgba(20, 25, 34, 0.7);
    color: #94a3b8;
    font-size: 0.82rem;
    font-weight: 600;
    margin-bottom: 0.9rem;
}

.home-badge .home-badge-icon {
    font-size: 0.95rem;
}

/* Streamlit's own [data-testid="stMarkdownContainer"] p base rule is more
   specific than a plain class selector and otherwise wins the cascade,
   silently pinning this at the default 16px - !important is needed on every
   property that rule also sets. */
.home-greeting {
    position: relative!important;
    z-index: 1!important;
    font-size: 2.3rem!important;
    font-weight: 700!important;
    letter-spacing: -0.02em!important;
    line-height: 1.15!important;
    margin: 0!important;
    background: linear-gradient(180deg, #ffffff 0%, #ffffff 55%, rgba(255, 255, 255, 0.65) 100%)!important;
    -webkit-background-clip: text!important;
    background-clip: text!important;
    -webkit-text-fill-color: transparent!important;
    display: inline-block!important;
}

/* The two Home action-card buttons: light gradient surface with dark text.
   Shape and hover/press motion come from the unified button block at the end
   of this stylesheet, shared with every other clickable button. */
.st-key-home_card_upload button,
.st-key-home_card_continue button {
    background: linear-gradient(180deg, #ffffff 0%, #f1f5f9 100%)!important;
    color: #0e1117!important;
    border: none!important;
    font-weight: 700!important;
}

.st-key-home_card_upload button p,
.st-key-home_card_continue button p {
    color: #0e1117!important;
    font-weight: 700!important;
}

/* Stat cards ("0 Days Streak", "11 Notes", ...): rectangular tiles with a
   muted label, a colored icon badge, and a big bold value - deliberately
   built from <div>/<span>, never <p>, since a plain class selector on a <p>
   loses to Streamlit's own more-specific [data-testid="stMarkdownContainer"]
   p rule (see .home-greeting above) and silently falls back to 16px text. */
.stat-card-row {
    display: flex;
    flex-wrap: wrap;
    gap: 1rem;
    margin: 0 0 1.4rem 0;
}

.stat-card {
    flex: 1 1 150px;
    background: linear-gradient(180deg, #161b22 0%, #11161d 100%);
    border: 1px solid #2c3340;
    border-radius: 16px;
    padding: 1rem 1.1rem;
}

.stat-card-top {
    display: flex;
    align-items: flex-start;
    justify-content: space-between;
    gap: 0.5rem;
    margin-bottom: 0.7rem;
}

.stat-card-label {
    color: #94a3b8;
    font-size: 0.85rem;
    font-weight: 600;
}

.stat-card-icon {
    width: 2rem;
    height: 2rem;
    border-radius: 10px;
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: 1.05rem;
    flex-shrink: 0;
}

.stat-card-value {
    color: #f8fafc;
    font-size: 1.7rem;
    font-weight: 800;
    letter-spacing: -0.01em;
    white-space: nowrap;
}

.home-section-title {
    color: #f8fafc;
    font-size: 1.05rem;
    font-weight: 700;
    margin: 0 0 0.6rem 0;
}

.week-row {
    display: flex;
    gap: 0.5rem;
    margin: 0 0 1.4rem 0;
}

.week-cell {
    flex: 1;
    text-align: center;
    background: #141922;
    border: 1px solid #2f3848;
    border-radius: 12px;
    padding: 0.55rem 0.2rem;
}

.week-cell.today {
    border-color: #5aa2ff;
    box-shadow: 0 0 0 1px rgba(90, 162, 255, 0.28);
}

.week-day-label {
    color: #94a3b8;
    font-size: 0.75rem;
    margin-bottom: 0.3rem;
}

.week-day-mark {
    font-size: 1.05rem;
    font-weight: 700;
    color: #4b5563;
}

.week-day-mark.done {
    color: #22c55e;
}

/* Upload Notes: turns the real (but visually tiny, in current Streamlit) file
   uploader into a big drag-and-drop card. The section below stays the real,
   functional drop target and file input - only its visible contents change;
   see _upload_dropzone_script(). */
/* Not "div[data-testid=...]": the dropzone is a <section>, and a tag-qualified
   selector silently matches nothing instead of erroring, which is exactly what
   happened here once already - kept tag-free so that can't recur. */
[data-testid="stFileUploaderDropzone"] {
    position: relative;
    min-height: 250px;
    border: 1px solid rgba(255, 255, 255, 0.1)!important;
    border-radius: 16px!important;
    background: #1b1b1d!important;
    box-shadow: 0 1px 2px rgba(0, 0, 0, 0.4), inset 0 0 50px rgba(255, 255, 255, 0.02);
    display: flex!important;
    flex-direction: column!important;
    align-items: center!important;
    justify-content: center!important;
    padding: 2.5rem 1rem!important;
    cursor: pointer;
    transition: transform 0.2s ease, box-shadow 0.25s ease, border-color 0.25s ease;
}

[data-testid="stFileUploaderDropzone"]:hover {
    transform: scale(1.01);
    box-shadow: 0 14px 34px -14px rgba(0, 0, 0, 0.7), inset 0 0 50px rgba(255, 255, 255, 0.02);
}

/* The blue beam: a bright arc racing around the box's outline, shown while the
   mouse is over it. The angle is a registered custom property so it can animate
   (the "<" of the type is written as a CSS escape - a literal one would be
   stripped by Streamlit's HTML sanitizer). */
@property --beam-angle {
    syntax: "\\3c angle>";
    inherits: false;
    initial-value: 0deg;
}
@keyframes upload-beam-spin { to { --beam-angle: 360deg; } }

[data-testid="stFileUploaderDropzone"]::before,
[data-testid="stFileUploaderDropzone"]::after {
    content: "";
    position: absolute;
    inset: -1px;
    border-radius: 17px;
    padding: 2px;
    background: conic-gradient(from var(--beam-angle), transparent 0deg, transparent 240deg, #5aa2ff 315deg, transparent 360deg);
    -webkit-mask: linear-gradient(#000 0 0) content-box, linear-gradient(#000 0 0);
    -webkit-mask-composite: xor;
    mask: linear-gradient(#000 0 0) content-box exclude, linear-gradient(#000 0 0);
    opacity: 0;
    transition: opacity 0.3s ease;
    animation: upload-beam-spin 4.6s linear infinite;
    pointer-events: none;
}
[data-testid="stFileUploaderDropzone"]::after { filter: blur(7px); padding: 4px; inset: -3px; border-radius: 19px; }
[data-testid="stFileUploaderDropzone"]:hover::before,
[data-testid="stFileUploaderDropzone"].is-dragging::before { opacity: 1; }
[data-testid="stFileUploaderDropzone"]:hover::after,
[data-testid="stFileUploaderDropzone"].is-dragging::after { opacity: 0.6; }

/* While a file is being dragged over the box */
[data-testid="stFileUploaderDropzone"].is-dragging {
    transform: scale(1.02);
    border-color: #5aa2ff!important;
    box-shadow: 0 0 0 4px rgba(90, 162, 255, 0.2), 0 14px 34px -14px rgba(0, 0, 0, 0.7);
}

/* The native "Upload" button and its size/type caption are hidden (not removed -
   they still work, see the script) in favor of the custom overlay below. */
[data-testid="stFileUploaderDropzone"] > span:has(button),
[data-testid="stFileUploaderDropzoneInstructions"] {
    display: none!important;
}

.upload-dropzone-overlay {
    display: flex;
    flex-direction: column;
    align-items: center;
    gap: 0.45rem;
    text-align: center;
}

.upload-dropzone-overlay .upload-dropzone-icon {
    position: relative;
    width: 72px;
    height: 72px;
    margin-bottom: 0.6rem;
    color: #a1a1aa;
    transition: color 0.3s ease;
}
.upload-dropzone-overlay .upload-dropzone-icon svg { width: 100%; height: 100%; display: block; filter: drop-shadow(0 1px 2px rgba(0, 0, 0, 0.4)); }
[data-testid="stFileUploaderDropzone"]:hover .upload-dropzone-icon,
[data-testid="stFileUploaderDropzone"].is-dragging .upload-dropzone-icon { color: #5aa2ff; }

/* a soft blue halo behind the cloud while dragging, and a gentle bob */
.upload-dropzone-overlay .upload-dropzone-icon::before {
    content: "";
    position: absolute;
    inset: -16px;
    border-radius: 50%;
    background: rgba(90, 162, 255, 0.12);
    filter: blur(10px);
    opacity: 0;
    transition: opacity 0.3s ease;
}
[data-testid="stFileUploaderDropzone"].is-dragging .upload-dropzone-icon::before { opacity: 1; }
@keyframes upload-cloud-bob { 0%, 100% { transform: translateY(0); } 50% { transform: translateY(-6px); } }
[data-testid="stFileUploaderDropzone"].is-dragging .upload-dropzone-icon { animation: upload-cloud-bob 1.5s ease-in-out infinite; }

.upload-dropzone-overlay .upload-dropzone-headline {
    color: #f4f4f5;
    font-weight: 600;
    font-size: 1.45rem;
}

.upload-dropzone-overlay .upload-dropzone-sub {
    color: #a1a1aa;
    font-size: 1.05rem;
}
.upload-dropzone-overlay .upload-dropzone-browse-link { color: #5aa2ff; font-weight: 600; }

.upload-dropzone-overlay .upload-dropzone-caption {
    color: #71717a;
    font-size: 0.85rem;
    margin-top: 0.1rem;
}

@media (prefers-reduced-motion: reduce) {
    [data-testid="stFileUploaderDropzone"]::before,
    [data-testid="stFileUploaderDropzone"]::after,
    [data-testid="stFileUploaderDropzone"].is-dragging .upload-dropzone-icon { animation: none; }
}

/* Instant "Saving your notes..." line - shown by JS the moment Save Notes is
   clicked, right below the button (the same spot Streamlit's own, slower to
   appear, spinner renders into - never a separate floating indicator). */
.instant-save-overlay {
    display: flex;
    align-items: center;
    gap: 0.6rem;
    color: #eef2ff;
    font-size: 0.95rem;
    font-weight: 600;
    margin-top: 0.75rem;
}

.instant-save-spin {
    width: 16px;
    height: 16px;
    border: 2px solid #2f3848;
    border-top-color: #5aa2ff;
    border-radius: 50%;
    animation: instant-save-spin-rotate 0.7s linear infinite;
    flex-shrink: 0;
}

@keyframes instant-save-spin-rotate {
    to { transform: rotate(360deg); }
}

/* Flashcards */
.flashcard-header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    margin: 0.25rem 0 1rem 0;
}

.flashcard-title {
    color: #f8fafc;
    font-size: 1.25rem;
    font-weight: 700;
    margin: 0;
}

.flashcard-count-pill {
    color: #94a3b8;
    font-size: 0.9rem;
    font-weight: 600;
    background: #171d29;
    border: 1px solid #2f3848;
    border-radius: 999px;
    padding: 0.25rem 0.85rem;
}

/* Wildcard match: every flashcard card is its own st.container(key=...), so
   this reaches all of them without a separate rule per card index. */
div[class*="st-key-flashcard_card_"] > div {
    border: 1px solid #2c3340;
    border-radius: 16px;
    background: linear-gradient(180deg, #161b22 0%, #11161d 100%);
    margin-bottom: 0.75rem;
    overflow: hidden;
}

div[class*="st-key-flashcard_card_"] [data-testid="stExpander"] {
    border: none;
    background: transparent;
}

div[class*="st-key-flashcard_card_"] [data-testid="stExpander"] summary {
    padding: 0.9rem 1.1rem;
}

div[class*="st-key-flashcard_card_"] [data-testid="stExpander"] summary p {
    color: #eef2ff;
    font-weight: 600;
    font-size: 0.98rem;
}

div[class*="st-key-flashcard_card_"] [data-testid="stExpanderDetails"] {
    padding: 0 1.1rem 1.1rem 1.1rem;
}

.flashcard-qa-label {
    color: #5aa2ff;
    font-size: 0.72rem;
    font-weight: 700;
    letter-spacing: 0.06em;
    text-transform: uppercase;
    margin: 0.7rem 0 0.3rem 0;
}

.flashcard-qa-label:first-child {
    margin-top: 0;
}

.flashcard-qa-text {
    color: #eef2ff;
    line-height: 1.55;
    font-size: 0.97rem;
}

.flashcard-qa-text.flashcard-answer {
    color: #dbe4f0;
}

/* ===== Unified button motion =====================================
   One shared look for every clickable button, ported from the indigo
   "Button" component: rounded-2xl shape, a drop shadow, a 4px lift + 2%
   grow on hover with an indigo glow, a light-indigo shine that sweeps across
   on hover, and a press-down shrink on click. It only ever adds shape,
   shadow and motion - never a background or text color - so each button
   keeps whatever colors it already had. Disabled buttons stay still. */
button:is(
    [data-testid="stBaseButton-secondary"],
    [data-testid="stBaseButton-primary"],
    [data-testid="stBaseButton-secondaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-tertiary"],
    [data-testid="stPopoverButton"]
),
.upload-dropzone-overlay .upload-dropzone-browse {
    position: relative;
    overflow: hidden;
    border-radius: 16px!important;
}

button:is(
    [data-testid="stBaseButton-secondary"],
    [data-testid="stBaseButton-primary"],
    [data-testid="stBaseButton-secondaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-tertiary"],
    [data-testid="stPopoverButton"]
):not(:disabled),
.upload-dropzone-overlay .upload-dropzone-browse,
[data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label,
div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label {
    cursor: pointer;
    transition: all 0.5s ease-out!important;
}

button:is(
    [data-testid="stBaseButton-secondary"],
    [data-testid="stBaseButton-primary"],
    [data-testid="stBaseButton-secondaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-tertiary"],
    [data-testid="stPopoverButton"]
):not(:disabled),
.upload-dropzone-overlay .upload-dropzone-browse {
    box-shadow: 0 25px 50px -12px rgba(0, 0, 0, 0.25);
}

/* Navigation / tab pills are radio labels dressed as buttons - same motion,
   but no base shadow so a selected pill keeps its existing highlight ring. */
[data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label,
div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label {
    position: relative;
    overflow: hidden;
}

/* Shine layer that sweeps across on hover. */
button:is(
    [data-testid="stBaseButton-secondary"],
    [data-testid="stBaseButton-primary"],
    [data-testid="stBaseButton-secondaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-tertiary"],
    [data-testid="stPopoverButton"]
):not(:disabled)::after,
.upload-dropzone-overlay .upload-dropzone-browse::after,
[data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label::after,
div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label::after {
    content: "";
    position: absolute;
    inset: 0;
    background: linear-gradient(to right, transparent, rgba(165, 180, 252, 0.4), transparent);
    transform: translateX(-100%);
    transition: transform 1s ease-out;
    pointer-events: none;
}

/* Keep the label/icon above the shine layer. */
button:is(
    [data-testid="stBaseButton-secondary"],
    [data-testid="stBaseButton-primary"],
    [data-testid="stBaseButton-secondaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-tertiary"],
    [data-testid="stPopoverButton"]
) > div,
[data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label > *,
div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label > * {
    position: relative;
    z-index: 1;
}

button:is(
    [data-testid="stBaseButton-secondary"],
    [data-testid="stBaseButton-primary"],
    [data-testid="stBaseButton-secondaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-tertiary"],
    [data-testid="stPopoverButton"]
):not(:disabled):hover,
.upload-dropzone-overlay .upload-dropzone-browse:hover,
[data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label:hover,
div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label:hover {
    transform: translateY(-4px) scale(1.02)!important;
    box-shadow: 0 25px 50px -12px rgba(99, 102, 241, 0.3), inset 0 0 24px rgba(129, 140, 248, 0.2)!important;
}

button:is(
    [data-testid="stBaseButton-secondary"],
    [data-testid="stBaseButton-primary"],
    [data-testid="stBaseButton-secondaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-tertiary"],
    [data-testid="stPopoverButton"]
):not(:disabled):hover::after,
.upload-dropzone-overlay .upload-dropzone-browse:hover::after,
[data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label:hover::after,
div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label:hover::after {
    transform: translateX(100%);
}

button:is(
    [data-testid="stBaseButton-secondary"],
    [data-testid="stBaseButton-primary"],
    [data-testid="stBaseButton-secondaryFormSubmit"],
    [data-testid="stBaseButton-primaryFormSubmit"],
    [data-testid="stBaseButton-tertiary"],
    [data-testid="stPopoverButton"]
):not(:disabled):active,
.upload-dropzone-overlay .upload-dropzone-browse:active,
[data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label:active,
div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label:active {
    transform: scale(0.95)!important;
}

@media (prefers-reduced-motion: reduce) {
    button:is(
        [data-testid="stBaseButton-secondary"],
        [data-testid="stBaseButton-primary"],
        [data-testid="stBaseButton-secondaryFormSubmit"],
        [data-testid="stBaseButton-primaryFormSubmit"],
        [data-testid="stBaseButton-tertiary"],
        [data-testid="stPopoverButton"]
    ):not(:disabled):hover,
    .upload-dropzone-overlay .upload-dropzone-browse:hover,
    [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label:hover,
    div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label:hover {
        transform: none!important;
    }
}
</style>
""", unsafe_allow_html=True)


# ===============================
# 5b. Preserve scroll position across reruns
# ===============================
# Streamlit's frontend tends to auto-scroll the page after a rerun triggered by
# a button inside a dynamically generated list (e.g. Rename/Delete in Manage
# Notes), since the widget list shifts position and it tries to keep the
# clicked element in view. This tracks the real scroll position continuously
# and forces it back after every rerun to cancel that out.
components.html(
    """
    <script>
    (function() {
        const KEY = "study_app_scroll_y";
        const w = window.parent;
        // Remember Light/Dark in the browser, so the next reload's very first frame is the right colour.
        try {
            const d = w.document;
            const sync = () => {
                const onSettings = d.querySelector(".st-key-settings_theme");
                const light = onSettings ? d.querySelector('.st-key-settings_theme input[value="0"]:checked') : d.querySelector(".nx-light-flag");
                if (light) { w.localStorage.setItem("nx-theme", "light"); d.documentElement.classList.add("nx-boot-light"); }
                else if (d.querySelector(".st-key-sb_user") || d.querySelector(".st-key-bh_hero")) { w.localStorage.setItem("nx-theme", "dark"); d.documentElement.classList.remove("nx-boot-light"); }
            };
            w.__nxThemeSyncFn = sync;   // the newest run's copy is the one that is called
            if (!w.__nxThemeClick) {
                w.__nxThemeClick = true;
                // the tile you press decides the colour in that same instant
                d.addEventListener("click", (e) => {
                    const tile = e.target && e.target.closest ? e.target.closest(".st-key-settings_theme label") : null;
                    if (!tile) return;
                    const light = /light/i.test(tile.textContent || "");
                    d.documentElement.classList.toggle("nx-boot-light", light);
                    try { w.localStorage.setItem("nx-theme", light ? "light" : "dark"); } catch (err) {}
                }, true);
            }
            if (!w.__nxThemeSync) {
                w.__nxThemeSync = true;
                new MutationObserver(() => w.__nxThemeSyncFn && w.__nxThemeSyncFn()).observe(d.body, {childList: true, subtree: true});
                w.setInterval(() => { try { w.__nxThemeSyncFn && w.__nxThemeSyncFn(); } catch (e) {} }, 600);
            }
            sync();
        } catch (e) {}
        // A reload (or back/forward) returns to the landing page already complete - no letter-by-letter
        // intro replaying - so it just settles in. A first visit keeps the intro.
        try {
            const nav = w.performance.getEntriesByType("navigation")[0];
            if (nav && (nav.type === "reload" || nav.type === "back_forward")) w.document.documentElement.classList.add("nx-reload");
        } catch (e) {}
        const getContainer = () => w.document.querySelector('[data-testid="stMain"]');

        const container = getContainer();
        if (container && !container.__scrollRestoreAttached) {
            container.__scrollRestoreAttached = true;
            container.addEventListener("scroll", () => {
                w.sessionStorage.setItem(KEY, container.scrollTop);
            });
        }

        const savedY = w.sessionStorage.getItem(KEY);
        if (savedY !== null) {
            const targetY = parseInt(savedY, 10);
            let attempts = 0;
            const restore = () => {
                const c = getContainer();
                if (c) c.scrollTop = targetY;
                attempts += 1;
                if (attempts < 15) {
                    w.requestAnimationFrame(restore);
                }
            };
            restore();
        }
    })();
    </script>
    """,
    height=0,
)


# Smooth page changes: each page renders in its own keyed container (see the
# `with st.container(key=f"page_...")` further down), which fades in when it
# mounts. Opacity only - a transform would turn the container into the
# containing block for the position:fixed top-bar pills inside it.
st.markdown(
    """
    <style>
    @keyframes page-fade-in { from { opacity: 0; } to { opacity: 1; } }
    [class*="st-key-page_"] { animation: page-fade-in 0.4s ease-out both; }
    @media (prefers-reduced-motion: reduce) { [class*="st-key-page_"] { animation: none; } }
    /* Streamlit greys the whole page to about a third while a rerun is in
       progress, which reads as a flicker on every page change. */
    [data-stale="true"], .stale-element, .element-container[data-stale="true"] {
        opacity: 1 !important; transition: none !important;
    }

    /* ---- Inputs & dropdowns: dark gray with a travelling blue "beam" ----
       Inside the signed-in pages only (the sign-in form keeps its own look).
       The one beam colour is the Home glow blue, #5aa2ff. */
    /* A seamless loop. The gradient image is twice the box's width and holds two identical beams
       exactly one box-width apart, so the pattern repeats every box-width. Sliding the image by
       exactly one box-width (0% -> 100%) therefore ends on a picture identical to the start: the
       beam that leaves the right edge is replaced by the next one entering from the left, with
       no restart. One box-width per 1.9s is about 550px/s, the same pace as the upload box's
       racing outline (one lap of its perimeter every 4.6s). */
    @keyframes nex-beam {
        0%   { background-position: 100% 0; }
        100% { background-position: 0% 0; }
    }
    [class*="st-key-page_"] [data-testid="stTextInputRootElement"],
    [class*="st-key-page_"] [data-testid="stSelectbox"] .react-aria-ComboBox > [role="group"],
    [class*="st-key-page_"] [data-testid="stMultiSelect"] .react-aria-ComboBox > [role="group"] {
        background: #1d1d1d !important;
        border: none !important;
        border-radius: 20px !important;
        box-shadow: inset 0 0 0 1px rgba(44,47,54,0.52), inset 0 0 50px 0 rgba(255,255,255,0.02) !important;
        position: relative;
        min-height: 44px;
        overflow: visible !important;
    }
    /* the beam: a bright segment of line sliding along the bottom edge ... */
    [class*="st-key-page_"] [data-testid="stTextInputRootElement"]::after,
    [class*="st-key-page_"] [data-testid="stSelectbox"] .react-aria-ComboBox > [role="group"]::after,
    [class*="st-key-page_"] [data-testid="stMultiSelect"] .react-aria-ComboBox > [role="group"]::after,
    /* ... and its soft glow just below it */
    [class*="st-key-page_"] [data-testid="stTextInputRootElement"]::before,
    [class*="st-key-page_"] [data-testid="stSelectbox"] .react-aria-ComboBox > [role="group"]::before,
    [class*="st-key-page_"] [data-testid="stMultiSelect"] .react-aria-ComboBox > [role="group"]::before {
        content: "";
        position: absolute;
        left: 16px; right: 16px; bottom: 0;
        height: 2px;
        border-radius: 2px;
        background: linear-gradient(90deg, transparent 0%, transparent 15%, #5aa2ff 25%, transparent 35%, transparent 65%, #5aa2ff 75%, transparent 85%, transparent 100%);
        background-size: 200% 100%;
        /* no end fade on purpose: as the beam slides out of the right edge the next one slides in
           from the left, so the total brightness stays constant and there is no dip or pop */
        animation: nex-beam 1.9s linear infinite;
        pointer-events: none;
        opacity: 0;                      /* hidden until the section is hovered */
        transition: opacity 0.3s ease;
    }
    [class*="st-key-page_"] [data-testid="stTextInputRootElement"]::before,
    [class*="st-key-page_"] [data-testid="stSelectbox"] .react-aria-ComboBox > [role="group"]::before,
    [class*="st-key-page_"] [data-testid="stMultiSelect"] .react-aria-ComboBox > [role="group"]::before { height: 10px; bottom: -4px; filter: blur(7px); }
    /* the beam only shows while the mouse is over the section */
    [class*="st-key-page_"] [data-testid="stTextInputRootElement"]:hover::after,
    [class*="st-key-page_"] [data-testid="stSelectbox"] .react-aria-ComboBox > [role="group"]:hover::after,
    [class*="st-key-page_"] [data-testid="stMultiSelect"] .react-aria-ComboBox > [role="group"]:hover::after { opacity: 1; }
    [class*="st-key-page_"] [data-testid="stTextInputRootElement"]:hover::before,
    [class*="st-key-page_"] [data-testid="stSelectbox"] .react-aria-ComboBox > [role="group"]:hover::before,
    [class*="st-key-page_"] [data-testid="stMultiSelect"] .react-aria-ComboBox > [role="group"]:hover::before { opacity: 0.55; }
    /* text, placeholder, arrows, chips */
    [class*="st-key-page_"] [data-testid="stTextInputRootElement"] input,
    [class*="st-key-page_"] .react-aria-ComboBox input {
        background: transparent !important; color: #e5e7eb !important; -webkit-text-fill-color: #e5e7eb !important;
        caret-color: #5aa2ff;
    }
    [class*="st-key-page_"] [data-testid="stTextInputRootElement"] input::placeholder { color: #565656 !important; -webkit-text-fill-color: #565656 !important; }
    [class*="st-key-page_"] .react-aria-ComboBox button svg { fill: #8b93a7 !important; color: #8b93a7 !important; }
    [class*="st-key-page_"] [data-testid="stMultiSelectTagsContainer"] span[role="group"] {
        background: rgba(90, 162, 255, 0.18) !important; color: #e5e7eb !important; border-radius: 10px !important;
    }
    [class*="st-key-page_"] [data-testid="stMultiSelectTagsContainer"] span[role="group"] * { color: #e5e7eb !important; fill: #e5e7eb !important; }
    /* the opened dropdown list (rendered outside the page, so matched globally) */
    body > div:has(> [data-testid="stSelectboxVirtualDropdown"]),
    [data-testid="stSelectboxVirtualDropdown"] {
        background: #1d1d1d !important;
        border-radius: 16px !important;
        box-shadow: 0 18px 40px -12px rgba(0,0,0,0.7), inset 0 0 0 1px rgba(44,47,54,0.7) !important;
        overflow: hidden;
    }
    [data-testid="stSelectboxVirtualDropdown"] [role="listbox"],
    [data-testid="stSelectboxVirtualDropdown"] [role="presentation"],
    [data-testid="stSelectboxVirtualDropdown"] [role="option"] { background: transparent !important; }
    [data-testid="stSelectboxVirtualDropdown"] [role="option"], [data-testid="stSelectboxVirtualDropdown"] [role="option"] * { color: #e5e7eb !important; }
    [data-testid="stSelectboxVirtualDropdown"] [role="option"]:hover,
    [data-testid="stSelectboxVirtualDropdown"] [role="option"][data-focused],
    [data-testid="stSelectboxVirtualDropdown"] [role="option"][aria-selected="true"] {
        background: rgba(90, 162, 255, 0.16) !important;
    }
    @media (prefers-reduced-motion: reduce) {
        [class*="st-key-page_"] [data-testid="stTextInputRootElement"]::after,
    [class*="st-key-page_"] [data-testid="stSelectbox"] .react-aria-ComboBox > [role="group"]::after,
    [class*="st-key-page_"] [data-testid="stMultiSelect"] .react-aria-ComboBox > [role="group"]::after { animation: none; }
    }
    </style>
    """,
    unsafe_allow_html=True,
)

# ===============================
# 5.5 Authentication gate
# ===============================
# Bridges Streamlit's own OAuth session (st.user, set after a successful
# st.login("google") round trip) into this app's existing authenticated flag,
# so the rest of the gate/sign-out logic only has to think about one flag
# regardless of whether the visitor signed in with email/password or Google.
# The name shown around the app (greeting, sidebar) is the account's full name.
# It's filled in when empty, and upgraded when all that's saved is the first name
# an older version stored - a name the user typed in themselves is left alone.
if st.session_state.get("authenticated"):
    _full_name, _ = _account_identity()
    _saved_name = (st.session_state.settings.get("display_name") or "").strip()
    if _full_name and _saved_name != _full_name and (not _saved_name or _saved_name == _full_name.split()[0]):
        st.session_state.settings["display_name"] = _full_name
        save_settings(st.session_state.settings)

# ===============================
# 6b. Light theme
# ===============================
# Light = white page background (the blue artwork still shows through, softly) with dark text.
# System Default is the dark design the app already has, so it adds nothing here. On the
# Settings page the tile you click previews straight away; everywhere else uses the saved choice.
_LIGHT_THEME_CSS = """
    <style>
    .stApp { background: #ffffff !important; }
    [data-testid='stMain'] {
        background: linear-gradient(rgba(255, 255, 255, 0.70), rgba(255, 255, 255, 0.70)), url(/app/static/home_background_light.png) center / cover no-repeat !important;
        color: #0f172a;
    }
    [data-testid='stHeader'] { background: transparent !important; }
    [data-testid='stHeader'] * { color: #0f172a !important; }
    [data-testid='stMain'] :is(h1, h2, h3, h4, h5, h6, p, li, label, summary, td, th, .home-section-title, .page-title, .app-subtitle) { color: #0f172a !important; }
    [data-testid='stMain'] [data-testid='stCaptionContainer'], [data-testid='stMain'] small { color: #475569 !important; }
    [data-testid='stMain'] [data-testid='stWidgetLabel'] p { color: #1e293b !important; }
    /* inputs and dropdowns */
    .stApp [class*="st-key-page_"] [data-testid="stTextInputRootElement"], .stApp [class*="st-key-page_"] [data-testid="stTextAreaRootElement"],
    .stApp [class*="st-key-page_"] [data-testid="stSelectbox"] .react-aria-ComboBox > [role="group"], .stApp [class*="st-key-page_"] [data-testid="stMultiSelect"] [role="group"]:not([aria-label]),
    .stApp [class*="st-key-page_"] [data-testid="stNumberInputContainer"] { background: #ffffff !important; border-color: #cbd5e1 !important; }
    .stApp [class*="st-key-page_"] input, .stApp [class*="st-key-page_"] textarea, .stApp [class*="st-key-page_"] [data-testid="stSelectbox"] * { color: #0f172a !important; -webkit-text-fill-color: #0f172a !important; }
    .stApp [class*="st-key-page_"] input::placeholder { color: #64748b !important; -webkit-text-fill-color: #64748b !important; }
    .stApp [data-testid="stMain"] [data-testid="stTab"], .stApp [data-testid="stMain"] [data-testid="stTab"] *, .stApp [data-testid="stMain"] button[role="tab"], .stApp [data-testid="stMain"] button[role="tab"] * { color: #475569 !important; }
    .stApp [data-testid="stMain"] [data-testid="stTab"][aria-selected="true"], .stApp [data-testid="stMain"] [data-testid="stTab"][aria-selected="true"] * { color: #2563eb !important; }
    .stApp [data-testid="stMain"] button[role="tab"][aria-selected="true"], .stApp [data-testid="stMain"] button[role="tab"][aria-selected="true"] * { color: #2563eb !important; }
    .stApp .st-key-save_notes_btn button:not(:disabled) { background: #5aa2ff !important; border: 1px solid #5aa2ff !important; }
    .stApp .st-key-save_notes_btn button:not(:disabled), .stApp .st-key-save_notes_btn button:not(:disabled) * { color: #ffffff !important; }
    .stApp .st-key-save_notes_btn button:disabled { background: rgba(90,162,255,0.35) !important; border-color: transparent !important; }
    .stApp .st-key-save_notes_btn button:disabled, .stApp .st-key-save_notes_btn button:disabled * { color: #ffffff !important; }
    /* Settings cards and tiles */
    .st-key-set_card_study, .st-key-set_card_gen, .st-key-set_card_look { background: rgba(255,255,255,0.92) !important; border-color: rgba(90,162,255,0.55) !important; box-shadow: 0 10px 30px -22px rgba(37,99,235,0.5) !important; }
    .st-key-page_Settings .set-h1, .set-title, .set-row-title { color: #0f172a !important; }
    .st-key-page_Settings .set-sub, .set-desc, .set-row-sub { color: #475569 !important; }
    .set-eyebrow { color: #2563eb !important; }
    .set-ic { background: rgba(90,162,255,0.16) !important; }
    .set-ic::before { background: #2563eb !important; }
    .st-key-settings_quiz_difficulty div[role="radiogroup"] { background: #f1f5f9 !important; }
    .st-key-settings_quiz_difficulty div[role="radiogroup"] label div { color: #334155 !important; }
    .st-key-settings_quiz_difficulty div[role="radiogroup"] label:has(input:checked) div, .st-key-settings_quiz_difficulty div[role="radiogroup"] label:has(input:checked) p { color: #ffffff !important; }
    .st-key-settings_theme div[role="radiogroup"] label { background: #f8fafc !important; border-color: #cbd5e1; }
    .st-key-settings_theme div[role="radiogroup"] label div, .st-key-settings_theme div[role="radiogroup"] label p { color: #1e293b !important; }
    .st-key-settings_theme div[role="radiogroup"] label:has(input:checked) { background: rgba(90,162,255,0.12) !important; border-color: #5aa2ff; }
    .st-key-set_toggle_shuffle, .st-key-set_toggle_examples { border-top-color: #e2e8f0 !important; }
    .st-key-settings_shuffle_questions label:not(:has(input:checked)) > div:first-of-type, .st-key-settings_auto_examples label:not(:has(input:checked)) > div:first-of-type { background: #cbd5e1 !important; }
    .st-key-settings_question_types [data-tag] { background: rgba(90,162,255,0.18) !important; }
    .stApp .st-key-settings_question_types [data-tag], .stApp .st-key-settings_question_types [data-tag] * { color: #1e3a8a !important; -webkit-text-fill-color: #1e3a8a !important; }
    .st-key-settings_save button, .st-key-settings_save button p { color: #ffffff !important; }
    /* opened drop-down lists and pop-overs (they live outside the page, so matched globally) */
    div:has(> [data-testid="stSelectboxVirtualDropdown"]), [data-testid="stSelectboxVirtualDropdown"] {
        background: #ffffff !important; box-shadow: 0 18px 40px -14px rgba(15,23,42,0.28), inset 0 0 0 1px #cbd5e1 !important;
    }
    [data-testid="stSelectboxVirtualDropdown"] [role="option"], [data-testid="stSelectboxVirtualDropdown"] [role="option"] * { color: #0f172a !important; -webkit-text-fill-color: #0f172a !important; }
    [data-testid="stSelectboxVirtualDropdown"] [role="option"]:hover, [data-testid="stSelectboxVirtualDropdown"] [role="option"][data-focused], [data-testid="stSelectboxVirtualDropdown"] [role="option"][aria-selected="true"] { background: rgba(90,162,255,0.18) !important; }
    [data-testid="stMultiSelectDropdown"] { background: #ffffff !important; border-radius: 16px !important; box-shadow: 0 18px 40px -14px rgba(15,23,42,0.28), inset 0 0 0 1px #cbd5e1 !important; overflow: hidden; }
    div:has(> [data-testid="stMultiSelectDropdown"]) { background: #ffffff !important; border-radius: 16px !important; }
    [data-testid="stMultiSelectDropdown"] [role="option"], [data-testid="stMultiSelectDropdown"] [role="option"] * { color: #0f172a !important; -webkit-text-fill-color: #0f172a !important; background: transparent !important; }
    [data-testid="stMultiSelectDropdown"] [role="option"]:hover, [data-testid="stMultiSelectDropdown"] [role="option"][data-focused], [data-testid="stMultiSelectDropdown"] [role="option"][aria-selected="true"] { background: rgba(90,162,255,0.18) !important; }
    [data-baseweb="popover"] > div, [data-testid="stPopoverBody"], [data-testid="stSelectboxVirtualDropdown"] ul { background: #ffffff !important; }
    [data-testid="stPopoverBody"], [data-testid="stPopoverBody"] * { color: #0f172a !important; }
    /* Home */
    .st-key-landing_links { background: rgba(255,255,255,0.92) !important; border-color: #cbd5e1 !important; }
    .home-badge { background: rgba(90,162,255,0.14) !important; border-color: rgba(90,162,255,0.5) !important; color: #1e3a8a !important; }
    .home-greeting { background: none !important; -webkit-text-fill-color: #0f172a !important; color: #0f172a !important; }
    .home-hero-glow { opacity: 0.55; }
    .stat-card { background: #ffffff !important; border-color: #dbe3ef !important; box-shadow: 0 8px 22px -18px rgba(37,99,235,0.45); }
    .stat-card-label { color: #475569 !important; }
    .stat-card-value, .home-section-title { color: #0f172a !important; }
    .week-cell { background: #ffffff !important; border-color: #dbe3ef !important; }
    .week-cell.today { border-color: #5aa2ff !important; }
    .week-day-label { color: #475569 !important; }
    .week-day-mark { color: #94a3b8 !important; }
    /* secondary buttons and pop-over buttons */
    [data-testid='stMain'] button[data-testid='stBaseButton-secondary'], [data-testid='stMain'] button[data-testid='stPopoverButton'] { background: #ffffff !important; border: 1px solid #cbd5e1 !important; color: #0f172a !important; }
    [data-testid='stMain'] button[data-testid='stBaseButton-secondary'] *, [data-testid='stMain'] button[data-testid='stPopoverButton'] * { color: #0f172a !important; }
    [data-testid='stMain'] button[data-testid='stBaseButton-primary'], [data-testid='stMain'] button[data-testid='stBaseButton-primary'] * { color: #ffffff !important; }
    /* Upload Notes */
    [data-testid='stFileUploaderDropzone'] { background: #f8fafc !important; border-color: #93b4e8 !important; }
    .upload-dropzone-overlay .upload-dropzone-headline { color: #0f172a !important; }
    .upload-dropzone-overlay .upload-dropzone-sub, .upload-dropzone-overlay .upload-dropzone-caption { color: #475569 !important; }
    /* Study Mode */
    .st-key-sm_doc_card { background: #ffffff !important; border-color: #dbe3ef !important; }
    .sm-doc-title, .sm-pdf { color: #0f172a !important; }
    .sm-badge { color: #334155 !important; background: #f1f5f9 !important; border-color: #dbe3ef !important; }
    /* About */
    .landing-card, .landing-step { background: #ffffff !important; border-color: #dbe3ef !important; }
    .landing-card h3 { color: #0f172a !important; }
    .landing-card p { color: #475569 !important; }
    [data-testid='stMain'] details { background: #ffffff !important; border-color: #dbe3ef !important; }
    [data-testid='stMain'] summary * { color: #0f172a !important; }
    </style>
    """


def _scope_light_css(css):
    """Prefix every rule so it only applies while the Light tile is checked (instant, in the
    browser, no rerun) or, on the other pages, while the saved-theme flag is on the page."""
    import re
    scope = 'body:is(:has(.nx-light-flag):not(:has(.st-key-page_Settings)), :has(.st-key-settings_theme input[value="0"]:checked))'
    css = re.sub(r"/\*.*?\*/", "", css, flags=re.S)
    css = re.sub(r"</?style>", "", css)
    out = []
    for block in css.split("}"):
        if "{" not in block:
            continue
        sels, body = block.split("{", 1)
        parts, depth, cur = [], 0, ""
        for ch in sels:
            if ch in "([":
                depth += 1
            elif ch in ")]":
                depth -= 1
            if ch == "," and depth == 0:
                parts.append(cur)
                cur = ""
            else:
                cur += ch
        parts.append(cur)
        scoped = []
        for s in parts:
            s = s.strip()
            if s.startswith(".stApp") or s.startswith("html"):
                scoped.append(scope + " " + s)
            else:
                scoped.append(scope + " " + s)
        out.append(", ".join(scoped) + " {" + body + "}")
    return "<style>" + "\n".join(out) + "</style>"


_LIGHT_THEME_SCOPED = _scope_light_css(_LIGHT_THEME_CSS)


def _apply_theme(saved_theme):
    # Always present (so toggling the Light tile can switch the page instantly in the browser).
    # The flag turns Light on from the saved choice (the Settings page follows the tile instead).
# Called as soon as sign-in is known, so the saved theme is on screen from the first paint.
    flag = "<div class='nx-light-flag' style='display:none'></div>" if saved_theme == "Light" else ""
    st.markdown(_LIGHT_THEME_SCOPED + flag, unsafe_allow_html=True)


# Signed-out visitors see only the landing hero (and the sign-in page once
# they press Get started / Log in / Sign up). The rest of the app - sidebar,
# dashboard, notes, study tools - is not shown until they sign in.
_landing_only = False
if st.session_state.get("authenticated"):
    st.session_state.show_auth = False
    _apply_theme(st.session_state.settings.get("theme", "Dark"))
    # Smooth sign-out: the moment Sign Out is pressed the whole window fades to the landing page's
    # dark colour (so none of the app shows while the server catches up), then fades away once the
    # landing page is up. No "<" in the script: it must survive the HTML sanitiser.
    st.html(
        "<script>(function(){"
        "if (window.__nxLeaveHook) return; window.__nxLeaveHook = true;"
        "document.addEventListener('click', function(e){"
        "var b = e.target && e.target.closest ? e.target.closest('.st-key-sidebar_sign_out button') : null;"
        "if (!b || document.getElementById('nx-leave')) return;"
        "var o = document.createElement('div'); o.id = 'nx-leave';"
        "o.style.cssText = 'position:fixed;inset:0;z-index:2147483000;background:#03061f;opacity:0;transition:opacity 0.35s ease;pointer-events:all;';"
        "document.body.appendChild(o);"
        "requestAnimationFrame(function(){ requestAnimationFrame(function(){ o.style.opacity = '1'; }); });"
        "var t0 = Date.now();"
        "var iv = setInterval(function(){"
        "var hero = document.querySelector('.st-key-bh_hero');"
        "var side = document.querySelector('[data-testid=\\'stSidebar\\']');"
        "var sideGone = !side || side.getBoundingClientRect().width === 0 || getComputedStyle(side).display === 'none';"
        "if ((hero && sideGone && Date.now() - t0 > 600) || Date.now() - t0 > 9000) {"
        "clearInterval(iv); o.style.transition = 'opacity 0.6s ease'; o.style.opacity = '0';"
        "setTimeout(function(){ o.remove(); }, 700); }"
        "}, 60);"
        "}, true);"
        "})();</script>",
        unsafe_allow_javascript=True,
    )
elif st.session_state.get("show_auth"):
    render_auth_page()
    st.stop()
else:
    _landing_only = True
    st.session_state.page = "Home"
    st.session_state.pop("pending_page", None)
    st.markdown(
        """
        <style>
        [data-testid="stSidebar"], [data-testid="stSidebarCollapsedControl"],
        .st-key-landing_links { display: none !important; }
        /* Full-bleed: no Streamlit header bar, and the hero is the whole window. */
        [data-testid="stHeader"], [data-testid="stToolbar"], [data-testid="stDecoration"] { display: none !important; }
        .stMainBlockContainer { padding: 0 !important; max-width: none !important; }
        .stMainBlockContainer > [data-testid="stVerticalBlock"] { gap: 0 !important; }
        .st-key-bh_hero {
            position: fixed !important; inset: 0 !important; width: 100vw !important;
            min-height: 100vh !important; height: 100vh !important; margin: 0 !important;
            border: 0 !important; border-radius: 0 !important; z-index: 5;
            padding: 0 7vw !important; gap: 0.5rem !important;
        }
        /* the Log in / Sign up pill floats over the image, in the corner */
        .stApp .st-key-landing_nav { top: 16px !important; right: 24px !important; }
        </style>
        """,
        unsafe_allow_html=True,
    )

# ===============================
# 6. Sidebar navigation
# ===============================
# Signed-out visitors never get a sidebar at all (not just a hidden one):
# building it for even a moment would flash the app's menu before the page
# styling arrives, and would leave stale menu items on screen during the
# move to the sign-in page.
if _landing_only:
    option = "Home"
else:
    if "page" not in st.session_state:
        st.session_state.page = "Home"

    if "pending_page" in st.session_state:
        st.session_state.page = st.session_state.pop("pending_page")

    # --- NexLearn sidebar: logo on top, full-width nav rows with outline icons, the
    # signed-in user pinned to the bottom. The radio below is still the real page
    # router (same key and options) - it is only restyled. ---
    def _sb_icon(inner: str) -> str:
        svg = (
            '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="none" stroke="#000" '
            'stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round">' + inner + "</svg>"
        )
        return "data:image/svg+xml;base64," + base64.b64encode(svg.encode()).decode("ascii")

    _sb_css = """
    <style>
    /* ---- the sidebar itself: 250px, full height, charcoal ---- */
    .stApp [data-testid="stSidebar"] {
        width: 250px !important; min-width: 250px !important; max-width: 250px !important;
        background: #191F29 !important;
        border-right: 1px solid rgba(255, 255, 255, 0.05);
    }
    .stApp [data-testid="stSidebar"] [data-testid="stSidebarContent"] {
        background: #191F29 !important; padding: 0 !important;
        display: flex; flex-direction: column; height: 100vh; overflow-y: auto;
    }
    /* always open at this width: no collapse arrow, no drag-to-resize handle */
    .stApp [data-testid="stSidebarHeader"],
    .stApp [data-testid="stSidebarCollapseButton"],
    .stApp [data-testid="stSidebarCollapsedControl"],
    .stApp [data-testid="stSidebar"] > div:not([data-testid]) { display: none !important; }  /* the drag handle, inside the sidebar */
    .stApp [data-testid="stSidebarUserContent"] {
        flex: 1; display: flex; flex-direction: column;
        width: 100% !important; margin: 0 !important; box-sizing: border-box;
        padding: 24px 14px 18px 14px !important;
    }
    .stApp [data-testid="stSidebarUserContent"] > div { flex: 1; display: flex; flex-direction: column; }
    .stApp [data-testid="stSidebarUserContent"] > div > [data-testid="stVerticalBlock"] { flex: 1; gap: 6px; }
    /* the user block's wrapper is the flex item of that column: auto top margin pushes it to the bottom */
    .stApp [data-testid="stSidebar"] [data-testid="stLayoutWrapper"]:has(> .st-key-sb_user) { margin-top: auto; }
    .stApp [data-testid="stSidebar"] [data-testid="stElementContainer"],
    .stApp [data-testid="stSidebar"] [data-testid="stRadio"] { width: 100% !important; }

    /* ---- logo ---- */
    .sb-logo img { width: 168px; display: block; margin: 0 0 20px 6px; }

    /* ---- navigation rows ---- */
    .stApp [data-testid="stSidebar"] [data-testid="stRadio"] [role="radiogroup"] {
        display: flex; flex-direction: column; gap: 6px; width: 100%;
    }
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label {
        width: 100% !important; height: 46px; box-sizing: border-box;
        display: flex !important; align-items: center; gap: 14px;
        margin: 0 !important; padding: 0 14px !important;
        border: none !important; border-radius: 12px !important;
        background: transparent !important; color: #aab3c2 !important;
        box-shadow: none !important; transform: none !important;
        transition: background-color 0.2s ease, color 0.2s ease !important;
        cursor: pointer; overflow: hidden;
    }
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label::after { display: none !important; }
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label:hover {
        background: rgba(255, 255, 255, 0.06) !important; color: #e8ecf3 !important;
        transform: none !important; box-shadow: none !important;
    }
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label:active { transform: none !important; }
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label:has(input:checked) {
        background: rgba(99, 102, 241, 0.30) !important; color: #ffffff !important;
    }
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label p {
        color: inherit !important; font-size: 16px !important; font-weight: 500 !important; line-height: 1.2 !important; margin: 0 !important;
    }
    /* Streamlit's own radio dot (a 16px circle just before the label text) */
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label > div > div > div:first-child:not([data-testid]) { display: none !important; }
    /* the row text takes the row's colour instead of Streamlit's dark default */
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label div,
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label [data-testid="stMarkdownContainer"] { color: inherit !important; }
    /* the outline icon, drawn from an SVG mask so it takes the row's text colour */
    .stApp [data-testid="stSidebar"] div[data-testid="stRadio"] div[role="radiogroup"] label::before {
        content: "" !important; display: block !important; flex: none;
        width: 22px !important; height: 22px !important; margin: 0 !important; padding: 0 !important;
        border: none !important; border-radius: 0 !important; box-shadow: none !important;
        background: currentColor !important;
        -webkit-mask: var(--sb-icon) center / contain no-repeat; mask: var(--sb-icon) center / contain no-repeat;
    }
    .stApp [data-testid="stSidebar"] [role="radiogroup"] label:nth-of-type(1)::before { --sb-icon: url("__HOME__"); }
    .stApp [data-testid="stSidebar"] [role="radiogroup"] label:nth-of-type(2)::before { --sb-icon: url("__UPLOAD__"); }
    .stApp [data-testid="stSidebar"] [role="radiogroup"] label:nth-of-type(3)::before { --sb-icon: url("__BOOK__"); }
    .stApp [data-testid="stSidebar"] [role="radiogroup"] label:nth-of-type(4)::before { --sb-icon: url("__GEAR__"); }
    .stApp [data-testid="stSidebar"] [role="radiogroup"] label:nth-of-type(5)::before { --sb-icon: url("__INFO__"); }

    /* ---- the signed-in user, pinned to the bottom ---- */
    .stApp .st-key-sb_user {
        padding-top: 16px; gap: 0 !important; flex: none !important;
        border-top: 1px solid rgba(255, 255, 255, 0.09);
    }
    .sb-user { display: flex; align-items: center; gap: 12px; }
    .sb-avatar {
        flex: none; width: 42px; height: 42px; border-radius: 50%;
        display: flex; align-items: center; justify-content: center;
        background: #4f5fe8; color: #ffffff; font-weight: 700; font-size: 15px; letter-spacing: 0.02em;
    }
    .sb-name { color: #f1f5f9; font-weight: 600; font-size: 15px; line-height: 1.2; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
    .stApp [data-testid="stSidebar"] .st-key-sidebar_sign_out button[data-testid] {
        width: auto !important; min-height: 0 !important; height: auto !important;
        margin: 4px 0 0 54px; padding: 6px 0 !important;
        background: transparent !important; border: none !important; border-radius: 8px !important;
        box-shadow: none !important; transform: none !important;
        color: #9aa4b2 !important; justify-content: flex-start !important; gap: 8px;
        transition: color 0.2s ease !important;
    }
    .stApp [data-testid="stSidebar"] .st-key-sidebar_sign_out button[data-testid]:hover {
        color: #ffffff !important; background: transparent !important; transform: none !important; box-shadow: none !important;
    }
    .stApp [data-testid="stSidebar"] .st-key-sidebar_sign_out button[data-testid]:active { transform: none !important; }
    .stApp [data-testid="stSidebar"] .st-key-sidebar_sign_out button::after { display: none !important; }
    .stApp [data-testid="stSidebar"] .st-key-sidebar_sign_out button::before {
        content: ""; flex: none; width: 17px; height: 17px;
        background: currentColor;
        -webkit-mask: url("__OUT__") center / contain no-repeat; mask: url("__OUT__") center / contain no-repeat;
    }
    .stApp [data-testid="stSidebar"] .st-key-sidebar_sign_out button p { color: inherit !important; font-size: 14px !important; margin: 0 !important; }
    </style>
    """
    _sb_css = (
        _sb_css
        .replace("__HOME__", _sb_icon('<path d="m3 9 9-7 9 7v11a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z"/><path d="M9 22V12h6v10"/>'))
        .replace("__UPLOAD__", _sb_icon('<path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><path d="m17 8-5-5-5 5"/><path d="M12 3v12"/>'))
        .replace("__BOOK__", _sb_icon('<path d="M2 3h6a4 4 0 0 1 4 4v14a3 3 0 0 0-3-3H2z"/><path d="M22 3h-6a4 4 0 0 0-4 4v14a3 3 0 0 1 3-3h7z"/>'))
        .replace("__GEAR__", _sb_icon('<path d="M12.22 2h-.44a2 2 0 0 0-2 2v.18a2 2 0 0 1-1 1.73l-.43.25a2 2 0 0 1-2 0l-.15-.08a2 2 0 0 0-2.73.73l-.22.38a2 2 0 0 0 .73 2.73l.15.1a2 2 0 0 1 1 1.72v.51a2 2 0 0 1-1 1.74l-.15.09a2 2 0 0 0-.73 2.73l.22.38a2 2 0 0 0 2.73.73l.15-.08a2 2 0 0 1 2 0l.43.25a2 2 0 0 1 1 1.73V20a2 2 0 0 0 2 2h.44a2 2 0 0 0 2-2v-.18a2 2 0 0 1 1-1.73l.43-.25a2 2 0 0 1 2 0l.15.08a2 2 0 0 0 2.73-.73l.22-.39a2 2 0 0 0-.73-2.73l-.15-.08a2 2 0 0 1-1-1.74v-.5a2 2 0 0 1 1-1.74l.15-.09a2 2 0 0 0 .73-2.73l-.22-.38a2 2 0 0 0-2.73-.73l-.15.08a2 2 0 0 1-2 0l-.43-.25a2 2 0 0 1-1-1.73V4a2 2 0 0 0-2-2z"/><circle cx="12" cy="12" r="3"/>'))
        .replace("__INFO__", _sb_icon('<circle cx="12" cy="12" r="10"/><path d="M12 16v-4"/><path d="M12 8h.01"/>'))
        .replace("__OUT__", _sb_icon('<path d="M9 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h4"/><path d="m16 17 5-5-5-5"/><path d="M21 12H9"/>'))
    )
    st.markdown(_sb_css, unsafe_allow_html=True)

    st.sidebar.markdown(
        "<div class='sb-logo'><img src='/app/static/nexlearn_logo_light.png' alt='NexLearn'/></div>",
        unsafe_allow_html=True,
    )
    option = st.sidebar.radio(
        "Choose a section:",
        ["Home", "Upload Notes", "Study Mode", "Settings", "About"],
        key="page",
        label_visibility="collapsed",
    )

    # Who is signed in: Google's name if that's how they signed in, otherwise the
    # name on the local account, otherwise their saved display name / email.
    _sb_name, _sb_email = _account_identity()
    if not _sb_name:
        _sb_name = (st.session_state.settings.get("display_name") or "").strip() or (_sb_email.split("@")[0] if _sb_email else "Account")
    _sb_initials = "".join(w[0] for w in _sb_name.split()[:2]).upper() or "?"

    with st.sidebar:
        with st.container(key="sb_user"):
            st.markdown(
                f"<div class='sb-user' title='{html.escape(_sb_email)}'><div class='sb-avatar'>{html.escape(_sb_initials)}</div>"
                f"<div class='sb-name'>{html.escape(_sb_name)}</div></div>",
                unsafe_allow_html=True,
            )
            if st.button("Sign Out", key="sidebar_sign_out"):
                st.session_state.signed_out = True
                st.logout()  # safe no-op if the session isn't a Google (st.login) one
                st.session_state.authenticated = False
                st.session_state.show_auth = False
                st.session_state.pending_page = "Home"
                st.rerun()


# ===============================
# 7. Home Page
# ===============================
st.markdown('<div id="study-top"></div>', unsafe_allow_html=True)
# Always one element here (an empty slot on Home/About, which open with their own
# headers), so the elements after it never shift position between pages.
_title_slot = st.empty()
if option not in ("Home", "About", "Upload Notes", "Study Mode", "Settings"):  # these have their own headings
    _title_slot.title("Study App 🚀")
st.markdown('<div id="top"></div>', unsafe_allow_html=True)

# Display streak (a placeholder, so finishing a quiz can update it in place).
# The Home page has its own richer greeting and stat row instead of this banner.
streak_header_slot = st.empty()
if option not in ("Home", "About", "Upload Notes", "Study Mode", "Settings"):
    streak_header_slot.markdown(streak_message(st.session_state.streak_data))

# ===============================
# 7a. Top-nav links (Home + About) and the About page
# ===============================
# Features / How It Works / FAQ are links in the top bar, in the middle and to
# the left of Log in / Sign up. They open the separate "About" page and scroll
# to the matching section. (Real buttons, not <a href>, so the session -
# guest data, sign-in - survives the page change.)
# Built on EVERY signed-in page (and just hidden where it doesn't belong), so the
# elements after it keep the same positions on every page. If it only existed on
# Home/About, switching pages would shift everything below it by one slot and
# Streamlit would briefly drop the previous page's widgets (the "Name your notes"
# box, Save Notes...) into the pill while it redraws.
if not _landing_only:
    # Every signed-in page (Home, Upload Notes, Study Mode, Settings, About) has the same
    # image as its page background: centred, scaled to cover, never repeated, and shown at
    # 30% opacity. The image file is the original, untouched; the 30% comes from a 70%
    # layer of the page's own dark colour (#0e1117, the .stApp background) laid over it,
    # which looks exactly like the image at 75% opacity over that colour. Content sits on
    # top of all of it. Streamlit's top bar is see-through so the image runs to the top.
    st.markdown(
        "<style>"
        "[data-testid='stMain'] { background: linear-gradient(rgba(14, 17, 23, 0.70), rgba(14, 17, 23, 0.70)), "
        "url(/app/static/home_background.png) center / cover no-repeat !important; }"
        "[data-testid='stHeader'] { background: transparent !important; }"
        + ("" if option in ("Home", "About") else ".st-key-landing_links { display: none !important; }")
        + "</style>",
        unsafe_allow_html=True,
    )
    st.markdown(
        """
        <style>
        [data-testid="stMain"], section.stMain, .stMain { scroll-behavior: smooth; }
        .st-key-landing_links {
            position: fixed !important;
            top: 0.7rem;
            left: calc(50% + 125px);
            transform: translateX(-50%);
            z-index: 1000000;
            width: auto !important;
            gap: 0.25rem !important;
            padding: 0.3rem 0.4rem;
            background: rgba(11, 16, 32, 0.92);
            border: 1px solid rgba(255,255,255,0.08);
            border-radius: 20px;
            backdrop-filter: blur(10px);
        }
        .stApp:has([data-testid="stSidebar"][aria-expanded="false"]) .st-key-landing_links { left: 50%; }
        .st-key-landing_links button {
            background: transparent !important;
            border: 1px solid transparent !important;
            padding: 0.35rem 0.95rem !important;
            min-height: 2.4rem;
        }
        .st-key-landing_links button p { color: #cbd5e1 !important; font-weight: 600 !important; font-size: 0.9rem !important; }
        .st-key-landing_links button:hover { background: rgba(99,102,241,0.22) !important; }
        .st-key-landing_links button:hover p { color: #ffffff !important; }
        @media (max-width: 1100px) {
            .st-key-landing_links, .stApp:has([data-testid="stSidebar"][aria-expanded="false"]) .st-key-landing_links {
                left: auto; right: calc(4.5rem + 235px); transform: none;
            }
        }
        @media (max-width: 640px) { .st-key-landing_links { display: none; } }

        /* Compact pills, vertically centred in Streamlit's 60px header strip
           (42px tall, 9px above and below) instead of overhanging its edge. */
        .stApp .st-key-landing_links, .stApp .st-key-landing_nav {
            top: 9px !important;
            height: 42px !important;
            box-sizing: border-box !important;
            padding: 0 0.3rem !important;
            align-items: center !important;
            gap: 0.2rem !important;
        }
        .stApp .st-key-landing_links button, .stApp .st-key-landing_nav button {
            min-height: 0 !important;
            height: 32px !important;
            min-width: 0 !important;
            padding: 0 0.75rem !important;
            border-radius: 12px !important;
        }
        .stApp .st-key-landing_nav button { min-width: 4.6rem !important; }
        .stApp .st-key-landing_links button p, .stApp .st-key-landing_nav button p {
            font-size: 0.8rem !important;
            line-height: 1 !important;
            margin: 0 !important;
            display: block !important;
        }
        /* Streamlit wraps the label in a 22px-line-height container, which leaves
           the (inline) label sitting low; match the container to the label so the
           text is truly centred in the button. */
        .stApp .st-key-landing_links button [data-testid="stMarkdownContainer"],
        .stApp .st-key-landing_nav button [data-testid="stMarkdownContainer"] {
            line-height: 1 !important;
            display: flex !important;
            align-items: center !important;
            justify-content: center !important;
        }
        </style>
        """,
        unsafe_allow_html=True,
    )
    with st.container(key="landing_links", horizontal=True):
        for _label, _target in (("Features", "features"), ("How It Works", "how-it-works"), ("FAQ", "faq")):
            if st.button(_label, key=f"nav_link_{_target}"):
                st.session_state.pending_page = "About"
                st.session_state.pending_scroll_target = _target
                st.rerun()

# Every page renders inside a container keyed by its name, so switching pages mounts
# a fresh container that fades in (see .st-key-page_* in the CSS) instead of the old
# page snapping to the new one.
with st.container(key=f"page_{option.replace(' ', '_')}"):
    if option == "About":
        st.markdown(
            """
            <style>
            .st-key-landing_nav {
                position: fixed !important; top: 0.7rem; right: 4.5rem; z-index: 1000000;
                width: auto !important; gap: 0.6rem !important; padding: 0.3rem 0.4rem;
                background: rgba(11, 16, 32, 0.92); border: 1px solid rgba(255,255,255,0.08);
                border-radius: 20px; backdrop-filter: blur(10px);
            }
            .st-key-landing_nav button { min-width: 6.2rem; padding: 0.35rem 1.1rem !important; }
            .st-key-landing_login button { background: transparent !important; border: 1px solid rgba(255,255,255,0.18) !important; }
            .st-key-landing_login button p { color: #e5e7eb !important; font-weight: 600 !important; }
            .st-key-landing_signup button { background: #f8fafc !important; border: 1px solid #f8fafc !important; }
            .st-key-landing_signup button p { color: #0b1020 !important; font-weight: 700 !important; }

            .about-wrap { padding-top: 2.5rem; }
            .landing-section { scroll-margin-top: 5rem; margin: 0 0 3rem 0; }
            .landing-section-head { text-align: center; margin-bottom: 1.4rem; }
            .landing-section-head h2 {
                color: #f8fafc; font-size: 1.9rem; font-weight: 800; letter-spacing: -0.02em;
                margin: 0 0 0.35rem 0 !important; padding: 0 !important;
            }
            .landing-section-head p { color: #98a2b3; margin: 0 !important; font-size: 1rem; }
            .landing-grid { display: grid; gap: 0.9rem; }
            .landing-grid.cols-4 { grid-template-columns: repeat(auto-fit, minmax(210px, 1fr)); }
            .landing-grid.cols-3 { grid-template-columns: repeat(auto-fit, minmax(240px, 1fr)); }
            .landing-card {
                background: linear-gradient(180deg, #161b22 0%, #11161d 100%);
                border: 1px solid #2c3340; border-radius: 16px; padding: 1.15rem 1.2rem;
                transition: transform 0.2s ease, border-color 0.2s ease;
            }
            .landing-card:hover { transform: translateY(-3px); border-color: rgba(99,102,241,0.55); }
            .landing-card-icon {
                width: 2.4rem; height: 2.4rem; border-radius: 12px; display: flex; align-items: center;
                justify-content: center; font-size: 1.15rem; margin-bottom: 0.7rem; background: rgba(99,102,241,0.18);
            }
            .landing-card h3 { color: #f8fafc; font-size: 1rem; font-weight: 700; margin: 0 0 0.3rem 0 !important; padding: 0 !important; }
            .landing-card p { color: #98a2b3; font-size: 0.9rem; line-height: 1.5; margin: 0 !important; }
            .landing-step-num {
                display: inline-flex; width: 1.9rem; height: 1.9rem; border-radius: 50%; align-items: center;
                justify-content: center; font-weight: 800; font-size: 0.9rem; color: #fff; margin-bottom: 0.7rem;
                background: linear-gradient(135deg, #6366f1, #8b5cf6);
            }
            .landing-faq { max-width: 760px; margin: 0 auto; display: grid; gap: 0.6rem; }
            .landing-faq details {
                background: linear-gradient(180deg, #161b22 0%, #11161d 100%);
                border: 1px solid #2c3340; border-radius: 14px; padding: 0.9rem 1.1rem;
            }
            .landing-faq details[open] { border-color: rgba(99,102,241,0.55); }
            .landing-faq summary { color: #f8fafc; font-weight: 600; cursor: pointer; }
            .landing-faq details p { color: #98a2b3; font-size: 0.92rem; line-height: 1.55; margin: 0.6rem 0 0 0 !important; }
            </style>
            """,
            unsafe_allow_html=True,
        )
        if not st.session_state.get("authenticated"):
            with st.container(key="landing_nav", horizontal=True):
                if st.button("Log in", key="landing_login"):
                    st.session_state.auth_view = "login"
                    st.session_state.show_auth = True
                    st.rerun()
                if st.button("Sign up", key="landing_signup"):
                    st.session_state.auth_view = "signup"
                    st.session_state.show_auth = True
                    st.rerun()

        def _landing_cards(items, cols):
            return (
                f"<div class='landing-grid cols-{cols}'>"
                + "".join(
                    f"<div class='landing-card'><div class='landing-card-icon'>{icon}</div>"
                    f"<h3>{title}</h3><p>{text}</p></div>"
                    for icon, title, text in items
                )
                + "</div>"
            )

        features_html = _landing_cards(
            [
                ("📄", "Upload any PDF", "Add your class notes and NexLearn reads the text for you."),
                ("🎯", "AI flashcards", "Key ideas turned into flashcards, in the amount you choose."),
                ("📝", "Smart quizzes", "Multiple choice, true/false and short answer with AI grading."),
                ("📈", "Track progress", "Streaks, quiz scores and study time, all in one place."),
            ],
            4,
        )
        steps = [
            ("Upload", "Add a PDF of your notes and give it a name."),
            ("Generate", "Create flashcards or a quiz from your notes in one click."),
            ("Study & track", "Review, take quizzes and watch your progress grow."),
        ]
        steps_html = (
            "<div class='landing-grid cols-3'>"
            + "".join(
                f"<div class='landing-card'><div class='landing-step-num'>{i}</div><h3>{t}</h3><p>{d}</p></div>"
                for i, (t, d) in enumerate(steps, 1)
            )
            + "</div>"
        )
        faqs = [
            ("Do I need an account?", "Yes. Sign up or log in (email, Google or Microsoft) to start. Your notes, quizzes and progress are saved to your account."),
            ("What files can I upload?", "PDF files. NexLearn extracts the text so it can build flashcards and quizzes."),
            ("How are flashcards and quizzes made?", "With AI from your own notes. If AI isn't available, NexLearn falls back to a built-in generator."),
            ("Can I change how many questions I get?", "Yes. Open Settings to set difficulty, question types, and flashcard and question counts."),
            ("What types of quiz questions are there?", "Multiple choice, true/false and short answer. Pick which ones you want in Settings. Short answers are graded by AI."),
            ("How does the study streak work?", "A day counts when you finish a quiz. Study on consecutive days to build your streak, and miss a day and it resets."),
            ("Where are my notes stored?", "Notes you save while logged in are stored locally on the device running NexLearn, not uploaded to a public site."),
            ("Can I rename or delete a note?", "Yes. Open Study Mode and use Manage Notes to rename or delete any of your saved notes."),
            ("Why did my PDF produce poor flashcards?", "NexLearn reads the text inside a PDF. Scanned pages that are only images have no text to read, so use a text-based PDF for the best results."),
            ("What do I get by logging in?", "Your notes, settings, streak, quiz history and study time are saved and come back the next time you log in."),
        ]
        faq_html = (
            "<div class='landing-faq'>"
            + "".join(f"<details><summary>{q}</summary><p>{a}</p></details>" for q, a in faqs)
            + "</div>"
        )
        st.markdown(
            "<div class='about-wrap'>"
            "<div id='features' class='landing-section'>"
            "<div class='landing-section-head'><h2>Features</h2><p>Everything you need to study smarter.</p></div>"
            f"{features_html}</div>"
            "<div id='how-it-works' class='landing-section'>"
            "<div class='landing-section-head'><h2>How It Works</h2><p>From notes to mastery in three steps.</p></div>"
            f"{steps_html}</div>"
            "<div id='faq' class='landing-section'>"
            "<div class='landing-section-head'><h2>FAQ</h2><p>Quick answers to common questions.</p></div>"
            f"{faq_html}</div>"
            "</div>",
            unsafe_allow_html=True,
        )

        if st.session_state.get("pending_scroll_target"):
            _target_id = st.session_state.pop("pending_scroll_target")
            components.html(f"""
            <script>
            setTimeout(() => {{
                const el = parent.document.querySelector('#{_target_id}');
                if (el) el.scrollIntoView({{behavior: 'smooth', block: 'start'}});
            }}, 400);
            </script>
            """, height=0)
        st.stop()  # nothing below belongs to the About page

    if option == "Home":
        notes = st.session_state.notes
        streak_n = streak_summary(st.session_state.streak_data)["streak"]

        # ===============================
        # Landing hero: auth buttons, logo, headline
        # ===============================
        # (The page background image is set for every signed-in page in the 7a block above.)
        st.markdown(
            """
            <style>
            .st-key-landing_nav {
                position: fixed !important;
                top: 0.7rem;
                right: 4.5rem;
                z-index: 1000000;
                width: auto !important;
                gap: 0.6rem !important;
                padding: 0.3rem 0.4rem;
                background: rgba(11, 16, 32, 0.92);
                border: 1px solid rgba(255,255,255,0.08);
                border-radius: 20px;
                backdrop-filter: blur(10px);
            }
            .st-key-landing_nav button { min-width: 6.2rem; padding: 0.35rem 1.1rem !important; }
            .st-key-landing_login button {
                background: transparent !important;
                border: 1px solid rgba(255,255,255,0.18) !important;
            }
            .st-key-landing_login button p { color: #e5e7eb !important; font-weight: 600 !important; }
            .st-key-landing_signup button {
                background: #f8fafc !important;
                border: 1px solid #f8fafc !important;
            }
            .st-key-landing_signup button p { color: #0b1020 !important; font-weight: 700 !important; }
            @keyframes landing-fade-up { from { opacity: 0; transform: translateY(14px); } to { opacity: 1; transform: none; } }
            .landing-hero { text-align: center; padding: 0.5rem 0 2.25rem 0; animation: landing-fade-up 0.5s ease-out both; }
            @media (prefers-reduced-motion: reduce) { .landing-hero { animation: none; } }
            .landing-logo {
                width: 190px; height: 190px; object-fit: cover; display: block; margin: 0 auto 0.5rem auto;
                border-radius: 28px;
                -webkit-mask-image: radial-gradient(circle at center, #000 58%, transparent 74%);
                mask-image: radial-gradient(circle at center, #000 58%, transparent 74%);
            }
            .landing-headline {
                font-size: clamp(2rem, 4.6vw, 3.6rem);
                font-weight: 800;
                line-height: 1.12;
                letter-spacing: -0.03em;
                max-width: 880px;
                margin: 0 auto 1.1rem auto !important;
                padding: 0 !important;
                text-align: center;
                background: linear-gradient(180deg, #ffffff 30%, #8b93a7 100%);
                -webkit-background-clip: text;
                background-clip: text;
                -webkit-text-fill-color: transparent;
                color: transparent;
            }
            .landing-sub {
                color: #98a2b3;
                font-size: clamp(1rem, 1.5vw, 1.2rem);
                line-height: 1.6;
                max-width: 620px;
                margin: 0 auto !important;
                text-align: center;
            }
            </style>
            """,
            unsafe_allow_html=True,
        )
        if not st.session_state.get("authenticated") and not _landing_only:
            # Pinned to the far upper-right corner like a site nav bar.
            with st.container(key="landing_nav", horizontal=True):
                if st.button("Log in", key="landing_login"):
                    st.session_state.auth_view = "login"
                    st.session_state.show_auth = True
                    st.rerun()
                if st.button("Sign up", key="landing_signup"):
                    st.session_state.auth_view = "signup"
                    st.session_state.show_auth = True
                    st.rerun()
        _logo_path = os.path.join("static", "nexlearn_logo.jpg")
        _logo_html = ""
        if os.path.exists(_logo_path):
            with open(_logo_path, "rb") as _f:
                _logo_html = (
                    "<img class='landing-logo' alt='NexLearn' src='data:image/jpeg;base64,"
                    + base64.b64encode(_f.read()).decode("ascii") + "'/>"
                )
        # The banner hero is only the signed-out first page; once signed in, Home
        # goes straight to the dashboard.
        if _landing_only:
            # Hero: the NexLearn banner (logo on a deep blue/violet glow) is the
            # background; the headline, subtext and buttons sit on the left over a dark
            # fade so they stay readable, and the logo sits on the right.
            # The original banner PNG, untouched (2048x768), served from static/ so the
            # browser downloads and caches it once instead of it riding along in the
            # page on every rerun.
            _banner_uri = "/app/static/nexlearn_banner.png"
            st.markdown(
                """
                <style>
                @keyframes landing-fade-up { from { opacity: 0; transform: translateY(14px); } to { opacity: 1; transform: none; } }
                .st-key-bh_hero {
                    position: relative; isolation: isolate; overflow: hidden;
                    background: #03061f; border-radius: 26px; border: 1px solid rgba(255,255,255,0.07);
                    min-height: 540px; padding: 3.2rem 3rem 3rem 3rem;
                    display: flex; flex-direction: column; justify-content: center;
                    animation: landing-fade-up 0.6s ease-out both;
                }
                /* the banner: its logo is centred in the image, and the image is placed so
                   that centre lands on the right of the hero */
                .st-key-bh_hero::before {
                    content: ""; position: absolute; top: 0; left: 72%; height: 100%;
                    aspect-ratio: 2048 / 768; transform: translateX(-50%); z-index: 0;
                    background: url(__BANNER__) center / 100% 100% no-repeat;
                    -webkit-mask-image: linear-gradient(90deg, transparent 0, #000 20%, #000 80%, transparent 100%);
                    mask-image: linear-gradient(90deg, transparent 0, #000 20%, #000 80%, transparent 100%);
                    will-change: transform;
                    animation: bh-drift 16s ease-in-out infinite;
                }
                /* a slow, gentle float and breathe - barely there, never jerky */
                @keyframes bh-drift {
                    0%, 100% { transform: translateX(-50%) translate(0, 0) scale(1); }
                    50%      { transform: translateX(-50%) translate(-6px, -10px) scale(1.03); }
                }
                @media (prefers-reduced-motion: reduce) { .st-key-bh_hero::before { animation: none; } }
                /* darkens the left so the copy stays readable */
                .st-key-bh_hero::after {
                    content: ""; position: absolute; inset: 0; z-index: 1; pointer-events: none;
                    background: linear-gradient(90deg, rgba(3,6,31,0.97) 0%, rgba(3,6,31,0.82) 34%, rgba(3,6,31,0) 64%);
                }
                .st-key-bh_hero > div { position: relative; z-index: 2; max-width: 31rem; }
                .bh-headline {
                    font-size: clamp(1.9rem, 3.4vw, 3.1rem); font-weight: 300 !important; line-height: 1.1;
                    letter-spacing: -0.03em; color: #f1f1f1 !important; margin: 0 0 1.2rem 0 !important; padding: 0 !important;
                }
                /* the dissolve out when Get started is clicked */
                @keyframes bh-leave {
                    from { opacity: 1; transform: scale(1); }
                    to   { opacity: 0; transform: scale(1.025); }
                }
                .st-key-bh_hero.bh-leaving {
                    animation: bh-leave 0.4s cubic-bezier(0.4, 0, 0.2, 1) forwards !important;
                    pointer-events: none;
                }
                /* no "copy link" anchor icon next to the headline */
                .st-key-bh_hero [data-testid="stHeaderActionElements"],
                .st-key-bh_hero [data-testid="stHeadingActionElements"],
                .st-key-bh_hero a[aria-label="Link to heading"] { display: none !important; }
                .bh-sub { color: rgba(255,255,255,0.65); font-size: 1rem; line-height: 1.6; max-width: 28rem; margin: 0 0 1.6rem 0 !important; }
                .st-key-bh_actions { gap: 0.75rem !important; }
                .st-key-bh_start button { background: #ffffff !important; border: 1px solid #ffffff !important; border-radius: 999px !important; padding: 0.55rem 1.6rem !important; }
                .st-key-bh_start button p { color: #000 !important; font-weight: 600 !important; }
                .st-key-bh_more button { background: transparent !important; border: 1px solid rgba(255,255,255,0.28) !important; border-radius: 999px !important; padding: 0.55rem 1.6rem !important; }
                .st-key-bh_more button p { color: rgba(255,255,255,0.9) !important; font-weight: 500 !important; }
                @media (max-width: 900px) {
                    .st-key-bh_hero { min-height: 640px; justify-content: flex-start; padding: 2.4rem 1.5rem; }
                    .st-key-bh_hero::before { left: 50%; top: auto; bottom: 0; height: 52%; }
                    .st-key-bh_hero::after { background: linear-gradient(180deg, rgba(3,6,31,0.97) 0%, rgba(3,6,31,0.85) 50%, rgba(3,6,31,0) 80%); }
                }
                </style>
                """.replace("__BANNER__", _banner_uri),
                unsafe_allow_html=True,
            )
            _hero_headline = "Upload your notes. Turn them into flashcards and quizzes built for better studying."
            _hero_sub = "Study, practice, and track your progress all in one place."

            def _gradual_spacing(text, delay_multiple, start_delay=0.0):
                """Gradual-spacing text: each character fades in while sliding in from
                20px to the left, one after another (0.5s each, `delay_multiple`
                seconds apart), beginning `start_delay` seconds after page load. Words
                stay together so wrapping behaves normally. Returns (html, the time
                the last character starts)."""
                i = 0
                words = []
                for word in text.split(" "):
                    chars = []
                    for ch in word:
                        chars.append(f"<span class='gs-char' style='animation-delay:{start_delay + i * delay_multiple:.2f}s'>{html.escape(ch)}</span>")
                        i += 1
                    words.append("<span class='gs-word'>" + "".join(chars) + "</span>")
                    i += 1  # the space after the word
                return " ".join(words), start_delay + (i - 1) * delay_multiple

            if _landing_only:
                # Reading order: the subtext must not start until the headline's last
                # letter has started, so it begins just after that moment.
                _hl_html, _hl_last_start = _gradual_spacing(_hero_headline, 0.04)
                _sub_html, _ = _gradual_spacing(_hero_sub, 0.025, _hl_last_start + 0.25)
                _hl_attr = f" aria-label='{html.escape(_hero_headline)}'"
                _sub_attr = f" aria-label='{html.escape(_hero_sub)}'"
                st.markdown(
                    """
                    <style>
                    .gs-word { display: inline-block; white-space: nowrap; }
                    .gs-char { display: inline-block; opacity: 0; animation: gs-in 0.5s ease-out forwards; }
                    @keyframes gs-in { from { opacity: 0; transform: translateX(-20px); } to { opacity: 1; transform: none; } }
                    /* Per-letter boxes lose kerning and run a touch wider; this width (in em, so it
                       scales with the headline) keeps the original three-line wrapping. */
                    .st-key-bh_hero > div { max-width: 34rem !important; }
                    .bh-headline { max-width: 11.9em; }
                    @media (prefers-reduced-motion: reduce) { .gs-char { animation: none; opacity: 1; } }
                    html.nx-reload .gs-char { animation: none !important; opacity: 1 !important; transform: none !important; }
                    </style>
                    """,
                    unsafe_allow_html=True,
                )
            else:
                _hl_html, _sub_html = html.escape(_hero_headline), html.escape(_hero_sub)
                _hl_attr = _sub_attr = ""

            with st.container(key="bh_hero"):
                st.markdown(
                    f"<h1 class='bh-headline'{_hl_attr}>{_hl_html}</h1>"
                    f"<p class='bh-sub'{_sub_attr}>{_sub_html}</p>",
                    unsafe_allow_html=True,
                )
                with st.container(key="bh_actions", horizontal=True):
                    if st.button("Get started", key="bh_start"):
                        if st.session_state.get("authenticated"):
                            st.session_state.pending_page = "Upload Notes"
                        else:
                            st.session_state.auth_view = "signup"
                            st.session_state.show_auth = True
                        st.rerun()
                    if not _landing_only and st.button("Learn more", key="bh_more"):
                        st.session_state.pending_page = "About"
                        st.rerun()

        if _landing_only:
            # Fade the hero out the instant Get started is clicked (in the browser,
            # before the server has even replied), so the move to the sign-in page
            # is a dissolve rather than a hard cut. No "<" in the script body -
            # Streamlit's sanitizer drops scripts containing one.
            st.html(
                "<script>(function(){"
                f"var _n='{uuid.uuid4().hex}';"
                "var d=window.parent.document;"
                "if(d.__bhLeaveBound)return;"
                "d.__bhLeaveBound=true;"
                "d.addEventListener('click',function(e){"
                "var t=e.target;"
                "if(!t||!t.closest||!t.closest('.st-key-bh_start'))return;"
                "var h=d.querySelector('.st-key-bh_hero');"
                "if(h)h.classList.add('bh-leaving');"
                "},true);})();</script>",
                unsafe_allow_javascript=True,
            )
            st.stop()  # signed out: the hero is the whole page

        # ===============================
        # Greeting
        # ===============================
        hour = datetime.now().hour
        if hour < 12:
            greeting = "Good morning"
        elif hour < 17:
            greeting = "Good afternoon"
        elif hour < 21:
            greeting = "Good evening"
        else:
            greeting = "Studying late"

        name = st.session_state.settings.get("display_name", "")
        badge_text = (
            f"🔥 {streak_n}-day streak — keep it going!" if streak_n > 0
            else "👋 Welcome back — start a streak today"
        )
        st.markdown(
            "<div class='home-hero-wrap'><div class='home-hero-glow'></div>"
            f"<div class='home-badge'>{html.escape(badge_text)}</div></div>",
            unsafe_allow_html=True,
        )
        col_greet, col_edit = st.columns([6, 1])
        with col_greet:
            greet_text = f"{greeting}, {name} 👋" if name else f"{greeting}! 👋"
            st.markdown(f"<p class='home-greeting'>{html.escape(greet_text)}</p>", unsafe_allow_html=True)
        with col_edit:
            with st.popover("✏️", use_container_width=True):
                new_name = st.text_input("Your name", value=name, key="settings_name_input", placeholder="e.g. Morikeh")
                if st.button("Save", key="settings_name_save", use_container_width=True):
                    st.session_state.settings["display_name"] = new_name.strip()
                    save_settings(st.session_state.settings)
                    st.rerun()
        st.markdown("<p class='app-subtitle'>Ready to keep studying?</p>", unsafe_allow_html=True)

        # ===============================
        # Stat row
        # ===============================
        stats = compute_overview_stats(notes)
        total_study_seconds = sum(load_study_time().values())

        stat_cards = [
            ("Day Streak", str(streak_n), "🔥", "#f97316"),
            ("Notes", str(stats["total_notes"]), "📚", "#5aa2ff"),
            ("Quiz Avg", f"{stats['avg_score']}%" if stats["total_quizzes"] else "—", "✅", "#22c55e"),
            ("Time Studied", format_study_duration(total_study_seconds), "⏱️", "#8b5cf6"),
        ]
        stat_card_html = "".join(
            "<div class='stat-card'>"
            "<div class='stat-card-top'>"
            f"<span class='stat-card-label'>{html.escape(label)}</span>"
            f"<span class='stat-card-icon' style='background:{color}33;'>{icon}</span>"
            "</div>"
            f"<div class='stat-card-value'>{html.escape(value)}</div>"
            "</div>"
            for label, value, icon, color in stat_cards
        )
        st.markdown(f"<div class='stat-card-row'>{stat_card_html}</div>", unsafe_allow_html=True)

        # ===============================
        # Action cards
        # ===============================
        continue_note = get_continue_note(notes)
        card_upload, card_continue = st.columns(2)
        with card_upload:
            with st.container(border=True):
                st.markdown("**📤 Upload Notes**")
                st.caption("Add a PDF / notes")
                if st.button("Upload a PDF →", key="home_card_upload", use_container_width=True):
                    st.session_state.pending_page = "Upload Notes"
                    st.rerun()
        with card_continue:
            with st.container(border=True):
                st.markdown("**▶️ Continue Studying**")
                if continue_note:
                    st.caption(continue_note["title"])
                    if st.button("Continue →", key="home_card_continue", use_container_width=True):
                        st.session_state.pending_page = "Study Mode"
                        st.session_state.pending_study_note = continue_note["id"]
                        st.rerun()
                else:
                    st.caption("Upload a note to get started")
                    st.button("Continue →", key="home_card_continue_disabled", use_container_width=True, disabled=True)

        # ===============================
        # Recent study material
        # ===============================
        st.markdown("<p class='home-section-title'>🗓️ Recent Study Material</p>", unsafe_allow_html=True)
        recent_notes = get_recent_notes(notes, limit=3)
        if not recent_notes:
            st.caption("Nothing studied yet — upload a note to begin.")
        else:
            for note_id, note, touched in recent_notes:
                row_title, row_date, row_go = st.columns([5, 2, 1])
                with row_title:
                    st.markdown(f"📄 {html.escape(note.get('title', 'Untitled'))}")
                with row_date:
                    st.caption(format_relative_study_date(touched))
                with row_go:
                    if st.button("→", key=f"home_recent_{note_id}", help="Study this note", use_container_width=True):
                        st.session_state.pending_page = "Study Mode"
                        st.session_state.pending_study_note = note_id
                        st.rerun()

        # ===============================
        # Notes library: the glass folder (React component, see nexlearn_folders.py)
        # ===============================
        _library = get_recent_notes(notes, limit=8) if notes else []
        if _library and nexlearn_folders.available():
            st.markdown("<p class='home-section-title'>🗂️ Your Notes Library</p>", unsafe_allow_html=True)
            _arts = ["aurora", "dusk", "ember", "verdant"]
            _picked = nexlearn_folders.glass_folders(
                [{
                    "id": "notes",
                    "label": "My Notes",
                    "meta": f"{len(notes)} note" + ("" if len(notes) == 1 else "s"),
                    "tone": "dark",
                    "art": "aurora",
                    "seed": 3,
                    "action": "none",
                    "files": [
                        {
                            "name": note.get("title", "Untitled"),
                            "meta": format_relative_study_date(touched),
                            "art": _arts[i % len(_arts)],
                        }
                        for i, (note_id, note, touched) in enumerate(reversed(_library))
                    ],
                }],
                key="home_notes_folder",
            )
            if _picked:
                _ids = [nid for nid, _n, _t in reversed(_library)]
                if 0 <= _picked.get("index", -1) < len(_ids):
                    st.session_state.pending_page = "Study Mode"
                    st.session_state.pending_study_note = _ids[_picked["index"]]
                    st.rerun()

        st.write("")

        # ===============================
        # This week's progress
        # ===============================
        st.markdown("<p class='home-section-title'>📈 Your Progress</p>", unsafe_allow_html=True)
        st.caption("This Week")
        studied_days = {d for d in (_parse_study_day(v) for v in st.session_state.streak_data.get("study_dates", [])) if d}
        today = date.today()
        monday = today - timedelta(days=today.weekday())
        day_letters = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
        week_cells = []
        for offset, label in enumerate(day_letters):
            d = monday + timedelta(days=offset)
            done = d in studied_days
            classes = "week-cell" + (" today" if d == today else "")
            mark_classes = "week-day-mark" + (" done" if done else "")
            week_cells.append(
                f"<div class='{classes}'><div class='week-day-label'>{label}</div>"
                f"<div class='{mark_classes}'>{'✓' if done else '–'}</div></div>"
            )
        st.markdown(f"<div class='week-row'>{''.join(week_cells)}</div>", unsafe_allow_html=True)

        # ===============================
        # Recommended next step
        # ===============================
        st.markdown("<p class='home-section-title'>🎯 Recommended Next Step</p>", unsafe_allow_html=True)
        recommendation = find_recommendation(notes)
        with st.container(border=True):
            if recommendation:
                rec_note_id, rec_note, rec_attempt = recommendation
                topics = rec_attempt.get("missed_topics") or []
                review_line = f"Review: {topics[0]}" if topics else "Review this note's material"
                st.markdown(
                    f"You scored **{rec_attempt.get('percentage', 0)}%** on "
                    f"*{html.escape(rec_note.get('title', 'Untitled'))}*"
                )
                st.caption(review_line)
                if st.button("Study Again →", key=f"home_study_again_{rec_note_id}", use_container_width=True):
                    st.session_state.pending_page = "Study Mode"
                    st.session_state.pending_study_note = rec_note_id
                    start_quiz_retake(rec_note_id, rec_note)
                    st.rerun()
            elif any(note.get("quiz_history") for note in notes.values()):
                st.markdown("🎉 Nice work — your recent quizzes are all 100%.")
            else:
                st.caption("Finish a quiz to get a personalized recommendation here.")


    # ===============================
    # 8. Upload Notes Page
    # ===============================
    elif option == "Upload Notes":
        # The whole form lives in a centred ~700px column with 24px between its parts.
        # The style and heading share one element, so they don't add an extra gap.
        st.markdown(
            """
            <style>
            .stMainBlockContainer { padding-top: 4.6rem !important; padding-bottom: 1.5rem !important; }  /* top clears Streamlit's 60px bar */
            /* the invisible helper elements above the page each add a 16px gap */
            .stMainBlockContainer > [data-testid="stVerticalBlock"] { gap: 0 !important; }
            .st-key-page_Upload_Notes { max-width: 700px; width: 100%; margin-left: auto; margin-right: auto; gap: 24px !important; }
            /* the zero-height script holders would each add a 24px gap */
            .st-key-page_Upload_Notes [data-testid="stElementContainer"]:has(> [data-testid="stHtml"]) { display: none; }
            .st-key-page_Upload_Notes .upm-title { color: #f8fafc !important; font-size: 1.9rem !important; font-weight: 800 !important; letter-spacing: -0.02em; line-height: 1.2 !important; text-align: center; margin: 0 !important; padding: 0 !important; }
            .st-key-page_Upload_Notes .upm-sub { color: #98a2b3 !important; font-size: 1rem !important; text-align: center; margin: 6px 0 0 0 !important; }
            .st-key-page_Upload_Notes [data-testid="stFileUploaderDropzone"] { min-height: 210px; padding: 1.5rem 1rem !important; }
            /* Save Notes: solid blue (the app's one blue, #5aa2ff) with white text */
            .st-key-save_notes_btn button:not(:disabled) {
                background: #5aa2ff !important; border: 1px solid #5aa2ff !important; color: #ffffff !important;
            }
            .st-key-save_notes_btn button:not(:disabled) p { color: #ffffff !important; font-weight: 700 !important; }
            .st-key-save_notes_btn button:disabled {
                background: rgba(90, 162, 255, 0.35) !important; border: 1px solid transparent !important; color: rgba(255, 255, 255, 0.75) !important;
            }
            .st-key-save_notes_btn button:disabled p { color: rgba(255, 255, 255, 0.75) !important; }
            </style>
            <p class='upm-title'>Add study material</p>
            <p class='upm-sub'>Upload a PDF to add it to your notes library.</p>
            """,
            unsafe_allow_html=True,
        )

        uploaded_file = st.file_uploader("Choose a PDF file", type=["pdf"], label_visibility="collapsed")
        try:
            max_upload_mb = int(st.get_option("server.maxUploadSize") or 200)
        except Exception:
            max_upload_mb = 200
        st.html(_upload_dropzone_script(max_upload_mb), unsafe_allow_javascript=True)

        if "note_title_input" not in st.session_state:
            st.session_state.note_title_input = ""

        if uploaded_file and st.session_state.get("last_uploaded_file_id") != uploaded_file.file_id:
            st.session_state.note_title_input = os.path.splitext(uploaded_file.name)[0]
            st.session_state.last_uploaded_file_id = uploaded_file.file_id

        title = st.text_input(
            "Name your notes",
            key="note_title_input",
            placeholder="e.g. Chapter 2 — x86-64 Architecture",
        )

        upload_signature = f"{uploaded_file.file_id}:{title}" if uploaded_file else None
        already_saved = uploaded_file is not None and st.session_state.get("last_saved_upload") == upload_signature

        if already_saved:
            if _persisting():
                st.success("Saved ✅ (This will still be here after refresh)")
            else:
                st.success("Added ✅ (Guest mode: this won't be saved - log in to keep your notes)")
            if st.button("📚 Go to Study Mode", use_container_width=True):
                st.session_state.pending_page = "Study Mode"
                st.rerun()
        else:
            can_save = uploaded_file is not None and title.strip() != ""
            col_l, col_mid, col_r = st.columns([1, 2, 1])
            with col_mid:
                save_clicked = st.button(
                    "Save Notes",
                    use_container_width=True,
                    disabled=not can_save,
                    help=None if can_save else "Choose a PDF and name it first",
                    key="save_notes_btn",
                )
                if can_save:
                    # A real save can take over a second (extracting text from a PDF
                    # isn't instant), and Streamlit itself doesn't flush its own
                    # spinner to the browser until that work yields the GIL back - so
                    # even the real spinner can visibly lag behind the click. This
                    # reacts to the actual browser click event directly, with no
                    # server round-trip, so the loading state appears the instant the
                    # button is pressed; it hands off to the real spinner once that
                    # arrives, and always clears itself once saving is done.
                    st.html(_instant_save_overlay_script(), unsafe_allow_javascript=True)
                if save_clicked and can_save:
                    # Stays inside col_mid, same as the button and the instant
                    # overlay above - st.spinner() called outside this column
                    # renders full-page-width instead, which visibly jumps the
                    # text away from the button once the real spinner takes over.
                    with st.spinner("Saving your notes..."):
                        note_id = uuid.uuid4().hex[:10]

                        # Save PDF file
                        # Guests' PDFs go to the OS temp folder (only so the preview can
                        # open them), never into the app's saved data.
                        if _persisting():
                            pdf_dir = PDF_DIR
                        else:
                            pdf_dir = os.path.join(tempfile.gettempdir(), "nexlearn_guest")
                            os.makedirs(pdf_dir, exist_ok=True)
                        pdf_path = os.path.join(pdf_dir, f"{note_id}.pdf")
                        with open(pdf_path, "wb") as f:
                            f.write(uploaded_file.getbuffer())

                        # Extract text (the slow part for a large or scanned PDF - this
                        # is what the spinner is really there for)
                        extracted_text = extract_text_from_pdf(uploaded_file)

                        # Save note data
                        notes = st.session_state.notes
                        notes[note_id] = {
                            "title": title,
                            "created_at": datetime.now().strftime("%Y-%m-%d %I:%M %p"),
                            "pdf_path": pdf_path,
                            "text": extracted_text,
                            "flashcards": [],
                            "quiz": [],
                            "quiz_history": []
                        }

                        st.session_state.notes = notes
                        save_notes(notes)

                        st.session_state.last_saved_upload = upload_signature
                    st.rerun()


    # ===============================
    # 9. Study Mode (THIS FIXES YOUR ISSUE)
    # ===============================
    elif option == "Study Mode":
        # ---- page styling: dark rounded cards, blue controls, 24px between sections ----
        _sm_css = """
        <style>
        .stMainBlockContainer { padding-top: 4.6rem !important; padding-bottom: 2rem !important; }
        .stMainBlockContainer > [data-testid="stVerticalBlock"] { gap: 0 !important; }
        .st-key-page_Study_Mode { gap: 24px !important; max-width: 1180px; }
        .st-key-page_Study_Mode .sm-title { color: #f8fafc !important; font-size: 2.3rem !important; font-weight: 800 !important; letter-spacing: -0.02em; line-height: 1.15 !important; margin: 0 !important; padding: 0 !important; }
        .st-key-page_Study_Mode .sm-sub { color: #aab3c2 !important; font-size: 1.15rem !important; margin: 6px 0 0 0 !important; }
        .st-key-page_Study_Mode .sm-label { color: #e5e9f0 !important; font-weight: 600 !important; font-size: 1rem !important; margin: 0 !important; }

        /* notes picker row: label on the left, Manage Notes link on the right */
        .st-key-sm_select { gap: 10px !important; }
        .st-key-sm_manage_toggle button[data-testid] {
            background: transparent !important; border: none !important; box-shadow: none !important; transform: none !important;
            color: #5aa2ff !important; font-weight: 600 !important; padding: 0 !important; min-height: 0 !important;
            width: auto !important; justify-content: flex-end !important; flex-direction: row-reverse; gap: 8px; font-size: 1rem !important;
        }
        .st-key-sm_manage_toggle, .st-key-sm_manage_toggle [data-testid="stButton"] { display: flex; justify-content: flex-end; width: 100%; }
        /* the notes dropdown: roomier, with the larger text from the mockup */
        .st-key-sm_select .react-aria-ComboBox > [role="group"] { min-height: 54px !important; border-radius: 16px !important; }
        .st-key-sm_select .react-aria-ComboBox input { font-size: 1.1rem !important; }
        .st-key-sm_manage_toggle button[data-testid]:hover { color: #8fc0ff !important; background: transparent !important; transform: none !important; box-shadow: none !important; }
        .st-key-sm_manage_toggle button::after { display: none !important; }
        .st-key-sm_manage_toggle button::before {
            content: ""; width: 18px; height: 18px; background: currentColor;
            -webkit-mask: url("__ARROW__") center / contain no-repeat; mask: url("__ARROW__") center / contain no-repeat;
        }
        .st-key-sm_manage_toggle button p { color: inherit !important; margin: 0 !important; }
        .st-key-sm_manage_panel { border: 1px solid rgba(255,255,255,0.08); border-radius: 16px; background: #151b27; padding: 16px 18px; gap: 12px !important; }

        /* the document card */
        .st-key-sm_doc_card { background: #151b27; border: 1px solid rgba(255,255,255,0.08); border-radius: 16px; padding: 20px 22px; }
        .sm-doc { display: flex; gap: 18px; align-items: center; }
        .sm-pdf {
            flex: none; width: 54px; height: 66px; display: flex; align-items: flex-end; justify-content: center; padding-bottom: 8px;
            background: linear-gradient(160deg, #ef5a4a, #c8382b); color: #fff; font-weight: 800; font-size: 0.78rem; letter-spacing: 0.04em;
            border-radius: 6px; clip-path: polygon(0 0, 68% 0, 100% 24%, 100% 100%, 0 100%);
        }
        .sm-doc-title { color: #f8fafc; font-size: 1.35rem; font-weight: 700; line-height: 1.25; overflow-wrap: anywhere; }
        .sm-doc-date { color: #9aa4b2; margin-top: 2px; font-size: 1rem; }
        .sm-badges { display: flex; flex-wrap: wrap; gap: 10px; margin-top: 12px; }
        .sm-badge { display: inline-flex; align-items: center; gap: 8px; padding: 7px 13px; border-radius: 10px; border: 1px solid rgba(255,255,255,0.1); background: rgba(255,255,255,0.03); color: #c3cbd8; font-size: 0.92rem; }
        .sm-badge::before { content: ""; width: 16px; height: 16px; flex: none; background: currentColor; -webkit-mask: var(--ic) center / contain no-repeat; mask: var(--ic) center / contain no-repeat; }
        .sm-i-cards::before { --ic: url("__CARDS__"); }
        .sm-i-quiz::before { --ic: url("__HELP__"); }
        .sm-i-clock::before { --ic: url("__CLOCK__"); }

        /* blue / outlined buttons (all keep their existing click behaviour) */
        [class*="st-key-preview_doc_"] button[data-testid] {
            background: transparent !important; border: 1px solid #5aa2ff !important; color: #ffffff !important;
            border-radius: 12px !important; gap: 8px; font-weight: 600 !important;
        }
        [class*="st-key-gen_"] button[data-testid]:not(:disabled), [class*="st-key-quiz_gen_"] button[data-testid]:not(:disabled),
        [class*="st-key-fc_next_"] button[data-testid]:not(:disabled) {
            background: #5aa2ff !important; border: 1px solid #5aa2ff !important; color: #ffffff !important; font-weight: 700 !important; gap: 10px;
        }
        [class*="st-key-gen_"] button[data-testid], [class*="st-key-quiz_gen_"] button[data-testid] { min-height: 52px !important; border-radius: 14px !important; }
        [class*="st-key-fc_prev_"] button[data-testid]:not(:disabled) {
            background: rgba(255,255,255,0.05) !important; border: 1px solid rgba(255,255,255,0.12) !important; color: #dbe2ee !important; gap: 8px;
        }
        [class*="st-key-fc_prev_"] button[data-testid]:disabled, [class*="st-key-fc_next_"] button[data-testid]:disabled {
            background: rgba(255,255,255,0.04) !important; border: 1px solid rgba(255,255,255,0.08) !important; color: rgba(255,255,255,0.35) !important;
        }
        [class*="st-key-preview_doc_"] button p, [class*="st-key-gen_"] button p, [class*="st-key-quiz_gen_"] button p,
        [class*="st-key-fc_reveal_"] button p, [class*="st-key-fc_next_"] button p, [class*="st-key-fc_prev_"] button p { color: inherit !important; margin: 0 !important; font-size: 1.05rem !important; }
        [class*="st-key-gen_"] button p, [class*="st-key-quiz_gen_"] button p { font-size: 1.15rem !important; }
        /* Streamlit stretches the label wrapper, which pushes the icon to the far edge */
        [class*="st-key-preview_doc_"] button[data-testid], [class*="st-key-gen_"] button[data-testid], [class*="st-key-quiz_gen_"] button[data-testid],
        [class*="st-key-fc_reveal_"] button[data-testid], [class*="st-key-fc_prev_"] button[data-testid], [class*="st-key-fc_next_"] button[data-testid] { justify-content: center !important; }
        [class*="st-key-preview_doc_"] button > div, [class*="st-key-gen_"] button > div, [class*="st-key-quiz_gen_"] button > div,
        [class*="st-key-fc_reveal_"] button > div, [class*="st-key-fc_prev_"] button > div, [class*="st-key-fc_next_"] button > div { flex: none !important; width: auto !important; }
        [class*="st-key-preview_doc_"] button::before, [class*="st-key-gen_"] button::before, [class*="st-key-quiz_gen_"] button::before,
        [class*="st-key-fc_reveal_"] button::before, [class*="st-key-fc_prev_"] button::before, [class*="st-key-fc_next_"] button::before {
            content: ""; width: 18px; height: 18px; flex: none; background: currentColor;
            -webkit-mask: var(--ic) center / contain no-repeat; mask: var(--ic) center / contain no-repeat;
        }
        [class*="st-key-fc_next_"] button[data-testid] { flex-direction: row-reverse; }
        [class*="st-key-preview_doc_"] button::before { --ic: url("__EXT__"); }
        [class*="st-key-gen_"] button::before { --ic: url("__CARDS__"); }
        [class*="st-key-quiz_gen_"] button::before { --ic: url("__HELP__"); }
        [class*="st-key-fc_reveal_"] button::before { --ic: url("__EYE__"); }
        [class*="st-key-fc_prev_"] button::before { --ic: url("__LEFT__"); }
        [class*="st-key-fc_next_"] button::before { --ic: url("__RIGHT__"); }

        /* Flashcards / Quiz tabs: underlined, not pills */
        div[class*="st-key-active_study_tab_"], div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] { width: 100% !important; }
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] {
            display: flex; flex-wrap: wrap; gap: 6px; border-bottom: 1px solid rgba(255,255,255,0.12); width: 100%;
        }
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label {
            height: auto !important; padding: 12px 18px !important; margin: 0 0 -1px 0 !important; border: none !important; border-bottom: 2px solid transparent !important;
            border-radius: 0 !important; background: transparent !important; box-shadow: none !important; transform: none !important;
            color: #c3cbd8 !important; transition: color 0.2s ease, border-color 0.2s ease !important;
        }
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label::after { display: none !important; }
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label:hover { color: #ffffff !important; transform: none !important; box-shadow: none !important; }
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label:has(input:checked) { color: #5aa2ff !important; border-bottom-color: #5aa2ff !important; background: transparent !important; box-shadow: none !important; }
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label > div > div > div:first-child:not([data-testid]) { display: none !important; }
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label div,
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label [data-testid="stMarkdownContainer"] { color: inherit !important; }
        div[class*="st-key-active_study_tab_"] div[data-testid="stRadio"] div[role="radiogroup"] label p { color: inherit !important; font-size: 1.02rem !important; font-weight: 600 !important; margin: 0 !important; }

        /* the flashcard viewer */
        .st-key-page_Study_Mode [data-testid="stElementContainer"]:has(#study-tabs) { height: 0; margin-bottom: -24px; }
        .st-key-page_Study_Mode [data-testid="stElementContainer"]:has(> [data-testid="stHtml"]) { display: none; }
        .fc-head { display: flex; align-items: baseline; justify-content: space-between; gap: 12px; }
        .st-key-page_Study_Mode .fc-title { color: #f8fafc !important; font-size: 1.5rem !important; font-weight: 800 !important; margin: 0 !important; }
        .st-key-page_Study_Mode .fc-count { color: #9aa4b2 !important; font-size: 1rem !important; white-space: nowrap; }
        /* the flip card */
        /* the row: all cards share one grid cell (so they are all the height of the tallest) and
           each is slid sideways by its position class. The one in the middle is sharp and big;
           the ones beside it are smaller, dimmer and blurred until clicked. */
        .fc-stack { display: grid; width: 100%; padding: 26px 0 30px; overflow: hidden; }
        .fc-stack-card {
            grid-area: 1 / 1; justify-self: center; width: 72%; perspective: 1600px; display: grid;
            transition: transform 0.65s cubic-bezier(0.22, 0.9, 0.3, 1), opacity 0.5s ease, filter 0.5s ease;
        }
        .fc-stack-card .fc-flipper { transition: transform 0.7s cubic-bezier(0.4, 0.2, 0.2, 1); }
        .fc-stack-card:not(.pos-0) .fc-flipper { transition: none; }   /* a card moving aside never spins */
        .fc-stack-card.pos-0 { z-index: 10; transform: none; opacity: 1; filter: none; cursor: pointer; }
        .fc-stack-card.pos-l1 { z-index: 9; transform: translateX(-60%) scale(0.86); opacity: 0.9; filter: blur(5px) brightness(0.7); cursor: pointer; }
        .fc-stack-card.pos-r1 { z-index: 9; transform: translateX(60%) scale(0.86); opacity: 0.9; filter: blur(5px) brightness(0.7); cursor: pointer; }
        .fc-stack-card.pos-l2 { z-index: 8; transform: translateX(-100%) scale(0.74); opacity: 0.55; filter: blur(7px) brightness(0.55); pointer-events: none; }
        .fc-stack-card.pos-r2 { z-index: 8; transform: translateX(100%) scale(0.74); opacity: 0.55; filter: blur(7px) brightness(0.55); pointer-events: none; }
        .fc-stack-card.pos-lfar { z-index: 7; transform: translateX(-100%) scale(0.74); opacity: 0; filter: blur(7px); pointer-events: none; }
        .fc-stack-card.pos-rfar { z-index: 7; transform: translateX(100%) scale(0.74); opacity: 0; filter: blur(7px); pointer-events: none; }
        .fc-stack-card.pos-l1:hover, .fc-stack-card.pos-r1:hover { filter: blur(3px) brightness(0.85); }
        @media (max-width: 760px) {
            .fc-stack-card { width: 82%; }
            .fc-stack-card.pos-l1 { transform: translateX(-54%) scale(0.86); }
            .fc-stack-card.pos-r1 { transform: translateX(54%) scale(0.86); }
        }
        .fc-flipper {
            display: grid; width: 100%; min-height: 300px; position: relative;
            transform-style: preserve-3d; transition: transform 0.7s cubic-bezier(0.4, 0.2, 0.2, 1);
        }
        .fc-flipper.is-flipped { transform: rotateY(180deg); }
        .fc-face {
            grid-area: 1 / 1; -webkit-backface-visibility: hidden; backface-visibility: hidden;
            display: flex; flex-direction: column; align-items: center; justify-content: center; gap: 14px; text-align: center;
            padding: 34px 30px; border-radius: 16px; border: 1px solid rgba(90,162,255,0.65); background: #0f1522;
            box-shadow: 0 0 0 1px rgba(90,162,255,0.12), 0 18px 50px -22px rgba(90,162,255,0.5);
        }
        .fc-back { transform: rotateY(180deg); background: linear-gradient(180deg, #11203a 0%, #0f1522 100%); }
        .fc-label { color: #5aa2ff; letter-spacing: 0.2em; font-size: 0.8rem; font-weight: 700; text-transform: uppercase; }
        .fc-q { color: #f8fafc; font-size: 1.85rem; font-weight: 800; line-height: 1.3; overflow-wrap: anywhere; }
        .fc-a { color: #eaf1fb; font-size: 1.4rem; font-weight: 600; line-height: 1.55; overflow-wrap: anywhere; }
        .fc-hint { color: #6b7686; font-size: 0.85rem; margin-top: 8px; }
        .fc-flip-wrap { display: flex; justify-content: center; margin-top: 22px; }
        .fc-flip-btn {
            display: inline-flex; align-items: center; gap: 10px; padding: 13px 30px; border-radius: 12px; cursor: pointer; user-select: none;
            background: #5aa2ff; color: #ffffff; font-weight: 700; font-size: 1.05rem;
            transition: transform 0.2s ease, box-shadow 0.2s ease, filter 0.2s ease;
        }
        .fc-flip-btn:hover { transform: translateY(-2px); filter: brightness(1.06); box-shadow: 0 12px 28px -12px rgba(90,162,255,0.7); }
        .fc-flip-btn:active { transform: scale(0.97); }
        .fc-flip-btn:focus-visible { outline: 2px solid #ffffff; outline-offset: 3px; }
        .fc-flip-btn::before { content: ""; width: 20px; height: 20px; background: currentColor; -webkit-mask: url("__FLIP__") center / contain no-repeat; mask: url("__FLIP__") center / contain no-repeat; }
        @media (prefers-reduced-motion: reduce) { .fc-flipper, .fc-stack-card { transition: none; } }
        .fc-nav { display: flex; align-items: center; justify-content: space-between; gap: 16px; margin-top: 26px; }
        .fc-nav-btn {
            display: inline-flex; align-items: center; justify-content: center; gap: 8px; min-width: 150px; height: 44px; padding: 0 22px;
            border-radius: 12px; cursor: pointer; user-select: none; font-weight: 600; font-size: 1.05rem;
            transition: transform 0.15s ease, background-color 0.2s ease, opacity 0.2s ease, filter 0.2s ease, box-shadow 0.2s ease;
        }
        .fc-nav-btn::before { content: ""; width: 18px; height: 18px; flex: none; background: currentColor; -webkit-mask: var(--ic) center / contain no-repeat; mask: var(--ic) center / contain no-repeat; }
        .fc-nav-prev { background: rgba(255,255,255,0.05); border: 1px solid rgba(255,255,255,0.12); color: #dbe2ee; --ic: url("__LEFT__"); }
        .fc-nav-next { background: #5aa2ff; border: 1px solid #5aa2ff; color: #ffffff; font-weight: 700; flex-direction: row-reverse; --ic: url("__RIGHT__"); }
        .fc-nav-btn:hover:not(.is-disabled) { transform: translateY(-2px); filter: brightness(1.08); }
        .fc-nav-next:hover:not(.is-disabled) { box-shadow: 0 12px 28px -12px rgba(90,162,255,0.7); }
        .fc-nav-btn:active:not(.is-disabled) { transform: scale(0.96); }
        .fc-nav-btn:focus-visible { outline: 2px solid #ffffff; outline-offset: 3px; }
        .fc-nav-btn.is-disabled { pointer-events: none; cursor: default; background: rgba(255,255,255,0.04); border: 1px solid rgba(255,255,255,0.08); color: rgba(255,255,255,0.35); }
        @media (max-width: 640px) {
            .fc-nav { flex-wrap: wrap; }
            .fc-nav-btn { flex: 1; min-width: 0; }
            .fc-dots { order: 3; width: 100%; }
        }
        .fc-dots { display: flex; gap: 12px; justify-content: center; align-items: center; flex-wrap: wrap; min-height: 46px; }
        .fc-dot { width: 9px; height: 9px; border-radius: 50%; background: #3a4558; }
        .fc-dot.on { width: 14px; height: 14px; background: #5aa2ff; box-shadow: 0 0 10px rgba(90,162,255,0.6); }
        @media (max-width: 900px) {
            .st-key-page_Study_Mode .sm-title { font-size: 1.9rem !important; }
            .fc-q { font-size: 1.45rem; }
            .sm-doc { align-items: flex-start; }
        }
        </style>
        """
        for _tag, _inner in {
            "__ARROW__": '<path d="M5 12h14"/><path d="m12 5 7 7-7 7"/>',
            "__CARDS__": '<rect width="14" height="14" x="8" y="8" rx="2" ry="2"/><path d="M4 16c-1.1 0-2-.9-2-2V4c0-1.1.9-2 2-2h10c1.1 0 2 .9 2 2"/>',
            "__HELP__": '<circle cx="12" cy="12" r="10"/><path d="M9.09 9a3 3 0 0 1 5.83 1c0 2-3 3-3 3"/><path d="M12 17h.01"/>',
            "__CLOCK__": '<circle cx="12" cy="12" r="10"/><path d="M12 6v6l4 2"/>',
            "__EXT__": '<path d="M15 3h6v6"/><path d="M10 14 21 3"/><path d="M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"/>',
            "__EYE__": '<path d="M2 12s3-7 10-7 10 7 10 7-3 7-10 7-10-7-10-7Z"/><circle cx="12" cy="12" r="3"/>',
            "__LEFT__": '<path d="m15 18-6-6 6-6"/>',
            "__RIGHT__": '<path d="m9 18 6-6-6-6"/>',
            "__FLIP__": '<path d="M3 12a9 9 0 0 1 9-9 9.75 9.75 0 0 1 6.74 2.74L21 8"/><path d="M21 3v5h-5"/><path d="M21 12a9 9 0 0 1-9 9 9.75 9.75 0 0 1-6.74-2.74L3 16"/><path d="M8 16H3v5"/>',
        }.items():
            _sm_css = _sm_css.replace(_tag, _sb_icon(_inner))
        st.markdown(
            _sm_css + "<p class='sm-title'>Study Mode</p><p class='sm-sub'>Choose your notes and start practicing.</p>",
            unsafe_allow_html=True,
        )

        notes = st.session_state.notes

        if not notes:
            st.info("No saved notes yet. Upload one first!")
        else:
            note_list = list(reversed(list(notes.items())))  # Show newest first
            note_id_options = [note_id for note_id, _ in note_list]

            # The dropdown identifies choices by their displayed label, so notes
            # that share a title must get distinct labels or picking any of them
            # lands on the same note. Only add a suffix where titles collide.
            title_counts = {}
            for note_id in note_id_options:
                t = notes[note_id].get("title", "Untitled")
                title_counts[t] = title_counts.get(t, 0) + 1

            note_labels = {}
            used_labels = set()
            for note_id in note_id_options:
                t = notes[note_id].get("title", "Untitled")
                label = t
                if title_counts[t] > 1:
                    label = f"{t} ({notes[note_id].get('created_at', 'unknown date')})"
                while label in used_labels:
                    label = f"{label} #{note_id[:4]}"
                used_labels.add(label)
                note_labels[note_id] = label

            # A "Continue studying" / "Study Again" button elsewhere (e.g. on Home)
            # hands off which note to open this way, same pattern as pending_page.
            if "pending_study_note" in st.session_state:
                pending_note_id = st.session_state.pop("pending_study_note")
                if pending_note_id in note_id_options:
                    st.session_state["study_mode_note_select"] = pending_note_id

            def _toggle_manage_notes():
                st.session_state["sm_manage_open"] = not st.session_state.get("sm_manage_open", False)

            # ---- notes dropdown, with Manage Notes on the right ----
            with st.container(key="sm_select"):
                label_col, manage_col = st.columns([3, 1], vertical_alignment="center")
                with label_col:
                    st.markdown("<p class='sm-label'>Select notes</p>", unsafe_allow_html=True)
                with manage_col:
                    st.button("Manage Notes", key="sm_manage_toggle", on_click=_toggle_manage_notes)
                selected_id = st.selectbox(
                    "Select a note to study:",
                    options=note_id_options,
                    format_func=lambda nid: note_labels[nid],
                    key="study_mode_note_select",
                    label_visibility="collapsed",
                )

            # ---- Manage Notes (view all + rename + delete), opened by the link above ----
            if st.session_state.get("sm_manage_open"):
                with st.container(key="sm_manage_panel"):
                    for note_id, note in note_list:
                        col_title, col_date, col_rename, col_delete = st.columns([3, 2, 1, 1])
                        with col_title:
                            new_title = st.text_input(
                                "Title",
                                value=note.get("title", "Untitled"),
                                key=f"rename_input_{note_id}",
                                label_visibility="collapsed"
                            )
                        with col_date:
                            st.caption(note.get("created_at", "unknown"))
                        with col_rename:
                            if st.button("✏️ Rename", key=f"rename_btn_{note_id}", use_container_width=True):
                                cleaned_title = new_title.strip()
                                if cleaned_title and cleaned_title != note.get("title"):
                                    notes[note_id]["title"] = cleaned_title
                                    st.session_state.notes = notes
                                    save_notes(notes)
                                st.rerun()
                        with col_delete:
                            if st.button("🗑️ Delete", key=f"delete_note_{note_id}", use_container_width=True):
                                pdf_path = note.get("pdf_path")
                                if pdf_path and os.path.exists(pdf_path):
                                    os.remove(pdf_path)
                                del notes[note_id]
                                st.session_state.notes = notes
                                save_notes(notes)
                                st.session_state.pop("study_mode_note_select", None)
                                st.rerun()

            if selected_id:
                sid = selected_id
                note = notes[sid]
                record_study_heartbeat()

                cards = note.get("flashcards") or []
                n_cards = len(cards)
                n_quiz = len(note.get("quiz") or [])

                # "Added Oct 8, 2026" from the saved timestamp (shown as-is if it can't be read)
                created_raw = note.get("created_at", "")
                try:
                    added_text = datetime.strptime(created_raw, "%Y-%m-%d %I:%M %p").strftime("%b %d, %Y").replace(" 0", " ")
                except (ValueError, TypeError):
                    added_text = created_raw or "unknown date"

                # Last practiced = the latest finished quiz attempt
                attempt_days = [d for d in (_parse_study_day(a.get("date")) for a in note.get("quiz_history", [])) if d]
                if not attempt_days:
                    practiced_text = "Not practiced yet"
                else:
                    last_day = max(attempt_days)
                    days_ago = (date.today() - last_day).days
                    practiced_text = "Today" if days_ago <= 0 else "Yesterday" if days_ago == 1 else last_day.strftime("%b %d, %Y").replace(" 0", " ")

                # ---- document card ----
                with st.container(key="sm_doc_card"):
                    info_col, preview_col = st.columns([5, 1.5], vertical_alignment="top")
                    with info_col:
                        st.markdown(
                            "<div class='sm-doc'><div class='sm-pdf'>PDF</div><div>"
                            f"<div class='sm-doc-title'>{html.escape(note.get('title', 'Untitled'))}</div>"
                            f"<div class='sm-doc-date'>Added {html.escape(added_text)}</div>"
                            "<div class='sm-badges'>"
                            f"<span class='sm-badge sm-i-cards'>{n_cards} flashcard{'s' if n_cards != 1 else ''}</span>"
                            f"<span class='sm-badge sm-i-quiz'>{n_quiz} quiz question{'s' if n_quiz != 1 else ''}</span>"
                            f"<span class='sm-badge sm-i-clock'>Last practiced: {html.escape(practiced_text)}</span>"
                            "</div></div></div>",
                            unsafe_allow_html=True,
                        )
                    with preview_col:
                        if st.button("Preview PDF", key=f"preview_doc_{sid}", use_container_width=True):
                            show_document_preview(note.get("title", "Untitled"), note.get("pdf_path", ""))

                # ---- generation buttons, side by side ----
                gen_fc_col, gen_quiz_col = st.columns(2)

                with gen_fc_col:
                    if st.button("Generate Flashcards", key=f"gen_{sid}", use_container_width=True):
                        user_settings = st.session_state.settings
                        with st.spinner("Generating flashcards..."):
                            flashcards, flashcards_source = generate_flashcards(
                                note["text"],
                                max_cards=user_settings["flashcard_count"],
                                explanation_level=user_settings["explanation_level"],
                                answer_length=user_settings["answer_length"],
                                auto_examples=user_settings["auto_examples"],
                            )
                        notes[sid]["flashcards"] = flashcards
                        st.session_state.notes = notes
                        save_notes(notes)
                        st.session_state[f"fc_index_{sid}"] = 0       # start the new set from card 1
                        st.session_state[f"fc_nav_{sid}"] = st.session_state.get(f"fc_nav_{sid}", 0) + 1  # face-up
                        source_label = "🤖 AI-generated" if flashcards_source == "ai" else "🧩 local generator"
                        st.success(f"✅ Generated {len(flashcards)} flashcards ({source_label})!")
                        st.markdown('[📇 Go to Flashcards](#study-tabs)')
                        st.rerun()

                with gen_quiz_col:
                    if st.button("Generate Quiz", key=f"quiz_gen_{sid}", use_container_width=True):
                        user_settings = st.session_state.settings
                        with st.spinner("Generating quiz..."):
                            quiz_questions, quiz_source = generate_quiz(
                                note["text"],
                                max_questions=user_settings["quiz_question_count"],
                                question_types=user_settings["question_types"],
                                difficulty=user_settings["quiz_difficulty"],
                                explanation_level=user_settings["explanation_level"],
                                answer_length=user_settings["answer_length"],
                                shuffle=user_settings["shuffle_questions"],
                            )
                        notes[sid]["quiz"] = quiz_questions
                        st.session_state.notes = notes
                        save_notes(notes)
                        # Initialize quiz state
                        st.session_state[f"quiz_started_{sid}"] = bool(quiz_questions)
                        st.session_state[f"quiz_current_{sid}"] = 0
                        st.session_state[f"quiz_score_{sid}"] = 0
                        st.session_state[f"quiz_answers_{sid}"] = {}
                        st.session_state[f"quiz_submitted_{sid}"] = False
                        st.session_state[f"quiz_results_saved_{sid}"] = False
                        st.session_state[f"active_study_tab_{sid}"] = "🎯 Quiz"
                        st.session_state.pending_scroll_target = "study-tabs"
                        if quiz_questions:
                            source_label = "🤖 AI-generated" if quiz_source == "ai" else "🧩 local generator"
                            st.toast(f"✅ Generated {len(quiz_questions)} questions ({source_label})")
                        else:
                            st.toast("⚠️ No valid quiz questions could be generated from this note yet.")
                        st.rerun()

                # ===============================
                # Study Tabs (FLASHCARDS | QUIZ)
                # ===============================
                if note.get("flashcards") or note.get("quiz") or note.get("text"):
                    st.markdown('<div id="study-tabs"></div>', unsafe_allow_html=True)

                    # The option strings are what the rest of the app stores and sets
                    # (e.g. generating a quiz jumps to "🎯 Quiz"); only what's shown
                    # on the tab changes, via format_func.
                    tabs_list = ["📇 Flashcards", "🎯 Quiz"]
                    if note.get("quiz_history") and len(note["quiz_history"]) > 0:
                        tabs_list.append("📊 Progress History")
                    tab_names = {
                        "📇 Flashcards": f"Flashcards ({n_cards})",
                        "🎯 Quiz": f"Quiz ({n_quiz})",
                        "📊 Progress History": "Progress History",
                    }

                    if f"active_study_tab_{sid}" not in st.session_state:
                        st.session_state[f"active_study_tab_{sid}"] = "📇 Flashcards" if cards else "🎯 Quiz"
                    elif st.session_state[f"active_study_tab_{sid}"] not in tabs_list:
                        st.session_state[f"active_study_tab_{sid}"] = tabs_list[0]

                    if tabs_list:
                        selected_tab = st.radio(
                            "Study section",
                            options=tabs_list,
                            format_func=lambda opt: tab_names.get(opt, opt),
                            horizontal=True,
                            key=f"active_study_tab_{sid}",
                            label_visibility="collapsed"
                        )

                        # ===============================
                        # SECTION: FLASHCARDS - one card at a time
                        # ===============================
                        if selected_tab == "📇 Flashcards":
                            if not cards:
                                st.info("No flashcards yet. Click `Generate Flashcards` above to create some for this note.")
                            else:
                                # Moving between cards happens entirely in the browser (see the script
                                # below), so Next / Previous / clicking a neighbour respond the instant
                                # you click - there is no server round trip to wait for.
                                #
                                # Every card is on the page. The CSS class of each (pos-0 in the middle,
                                # pos-l1 / pos-l2 to its left, pos-r1 / pos-r2 to its right) decides where
                                # it sits, and changing those classes is what slides the row. The class of
                                # every card also carries the identity of this set of cards, so generating a
                                # new set (or switching notes) starts again from card 1, face-up.
                                set_id = hashlib.md5(
                                    "\x1e".join(f"{c.get('q', '')}\x1f{c.get('a', '')}" for c in cards).encode("utf-8")
                                ).hexdigest()[:8]
                                set_cls = f"fc-s-{sid}-{set_id}"

                                stack_html = ""
                                for i, card in enumerate(cards):
                                    # Re-normalized here (not just at generation time) so
                                    # flashcards saved before a text-cleanup fix - e.g. the
                                    # PUA "tofu box" bullet characters some PDFs produce -
                                    # still display cleanly without needing a regenerate.
                                    q_i = normalize_quiz_sentence(card.get("q", ""))
                                    a_i = normalize_quiz_sentence(card.get("a", ""))
                                    if i == 0:
                                        pos = "pos-0"
                                    else:
                                        pos = f"pos-r{i}" if i <= 2 else "pos-rfar"
                                    stack_html += (
                                        f"<div class='fc-stack-card {pos} {set_cls}'>"
                                        "<div class='fc-flipper'>"
                                        "<div class='fc-face fc-front'>"
                                        "<div class='fc-label'>Question</div>"
                                        f"<div class='fc-q'>{html.escape(q_i)}</div>"
                                        "<div class='fc-hint'>Click the card to flip it</div>"
                                        "</div>"
                                        "<div class='fc-face fc-back'>"
                                        "<div class='fc-label'>Answer</div>"
                                        f"<div class='fc-a'>{html.escape(a_i)}</div>"
                                        "</div></div></div>"
                                    )
                                dots = "".join(f"<span class='fc-dot{' on' if i == 0 else ''}'></span>" for i in range(n_cards))
                                st.markdown(
                                    "<div class='fc-head'><p class='fc-title'>Review your flashcards</p>"
                                    f"<span class='fc-count'>Card 1 of {n_cards}</span></div>",
                                    unsafe_allow_html=True,
                                )
                                st.markdown(
                                    f"<div class='fc-stack'>{stack_html}</div>"
                                    "<div class='fc-flip-wrap'><div class='fc-flip-btn' role='button' tabindex='0'>Flip Card</div></div>"
                                    "<div class='fc-nav'>"
                                    "<div class='fc-nav-btn fc-nav-prev is-disabled' role='button' tabindex='0'>Previous</div>"
                                    f"<div class='fc-dots'>{dots}</div>"
                                    f"<div class='fc-nav-btn fc-nav-next{' is-disabled' if n_cards <= 1 else ''}' role='button' tabindex='0'>Next</div>"
                                    "</div>",
                                    unsafe_allow_html=True,
                                )
                                # One handler for the whole page, bound once. It owns the card position:
                                # it re-labels the cards, the "Card X of Y" count, the dots and the
                                # Previous / Next state itself. (No "<" anywhere in the body - Streamlit's
                                # sanitizer drops scripts containing one.)
                                _fc_js = """
                                var d=window.parent.document;
                                if(d.__fcRowBound)return;
                                d.__fcRowBound=true;
                                d.__fcPos={};
                                function stackEl(){return d.querySelector('.fc-stack');}
                                function cards(){var s=stackEl();return s?Array.prototype.slice.call(s.querySelectorAll('.fc-stack-card')):[];}
                                function cur(){var c=cards();for(var i=0;c.length>i;i++){if(c[i].classList.contains('pos-0'))return i;}return 0;}
                                function setKey(){var c=cards();if(!c.length)return '';var cl=c[0].classList;for(var j=0;cl.length>j;j++){if(cl[j].indexOf('fc-s-')===0)return cl[j];}return '';}
                                function posClass(o){if(o===0)return 'pos-0';if(o>0)return o>2?'pos-rfar':'pos-r'+o;return o>-3?'pos-l'+(-o):'pos-lfar';}
                                function setOn(el,name,on){if(el&&el.classList.contains(name)!==on){el.classList.toggle(name,on);}}
                                function sync(){
                                  var c=cards();var n=c.length;if(!n)return;
                                  var s=stackEl();var k=cur();
                                  if(!s.getAttribute('data-restored')){s.setAttribute('data-restored','1');var saved=d.__fcPos[setKey()];if(saved&&saved>0&&n>saved){show(saved);return;}}
                                  var cnt=d.querySelector('.fc-count');var txt='Card '+(k+1)+' of '+n;if(cnt&&cnt.textContent!==txt)cnt.textContent=txt;
                                  var dots=d.querySelectorAll('.fc-dot');for(var i=0;dots.length>i;i++){setOn(dots[i],'on',i===k);}
                                  setOn(d.querySelector('.fc-nav-prev'),'is-disabled',k===0);
                                  setOn(d.querySelector('.fc-nav-next'),'is-disabled',k===n-1);
                                }
                                function show(k){
                                  var c=cards();
                                  for(var i=0;c.length>i;i++){
                                    var want=posClass(i-k);var cl=c[i].classList;var have=null;
                                    for(var j=0;cl.length>j;j++){if(cl[j].indexOf('pos-')===0){have=cl[j];break;}}
                                    if(have!==want){if(have)cl.remove(have);cl.add(want);}
                                    var f=c[i].querySelector('.fc-flipper');
                                    if(f&&f.classList.contains('is-flipped'))f.classList.remove('is-flipped');
                                  }
                                  d.__fcPos[setKey()]=k;
                                  sync();
                                }
                                function go(delta){var c=cards();if(!c.length)return;var k=cur();var t=Math.max(0,Math.min(c.length-1,k+delta));if(t!==k)show(t);}
                                function flip(){var f=d.querySelector('.fc-stack-card.pos-0 .fc-flipper');if(f)f.classList.toggle('is-flipped');}
                                d.addEventListener('click',function(e){
                                  var t=e.target;if(!t||!t.closest)return;
                                  if(t.closest('.fc-nav-next'))go(1);
                                  else if(t.closest('.fc-nav-prev'))go(-1);
                                  else if(t.closest('.fc-stack-card.pos-r1'))go(1);
                                  else if(t.closest('.fc-stack-card.pos-l1'))go(-1);
                                  else if(t.closest('.fc-stack-card.pos-0, .fc-flip-btn'))flip();
                                },true);
                                d.addEventListener('keydown',function(e){
                                  var t=e.target;if(!t||!t.classList)return;
                                  if(e.key==='Enter'||e.key===' '){
                                    if(t.classList.contains('fc-flip-btn')){e.preventDefault();flip();}
                                    else if(t.classList.contains('fc-nav-next')){e.preventDefault();go(1);}
                                    else if(t.classList.contains('fc-nav-prev')){e.preventDefault();go(-1);}
                                  } else if((e.key==='ArrowRight'||e.key==='ArrowLeft')&&stackEl()&&!(t.closest&&t.closest('input,textarea,select,[role=listbox],[role=radiogroup],[role=combobox]'))){
                                    go(e.key==='ArrowRight'?1:-1);
                                  }
                                },true);
                                new MutationObserver(function(){sync();}).observe(d.body,{subtree:true,childList:true,attributes:true,attributeFilter:['class']});
                                sync();
                                """
                                st.html("<script>(function(){" + _fc_js + "})();</script>", unsafe_allow_javascript=True)

                        # ===============================
                        # SECTION: QUIZ
                        # ===============================
                        if selected_tab == "🎯 Quiz":
                            st.subheader("Take Your Quiz")
                        
                            # Initialize quiz state if not already done
                            if f"quiz_started_{sid}" not in st.session_state:
                                st.session_state[f"quiz_started_{sid}"] = False
                                st.session_state[f"quiz_current_{sid}"] = 0
                                st.session_state[f"quiz_score_{sid}"] = 0
                                st.session_state[f"quiz_answers_{sid}"] = {}
                                st.session_state[f"quiz_submitted_{sid}"] = False
                                st.session_state[f"quiz_results_saved_{sid}"] = False

                            if not note.get("quiz"):
                                st.info("No quiz is ready yet. Click `Generate Quiz` above to create one for this note.")
                                st.caption("If no questions are generated, the cleaned passage may still be too short or too noisy for the current validator.")

                            # Check if quiz is in progress
                            elif st.session_state.get(f"quiz_started_{sid}"):
                                    current_q_idx = st.session_state[f"quiz_current_{sid}"]
                                    quiz_list = note["quiz"]
                                    total_q = len(quiz_list)
                                
                                    # Check if quiz is complete
                                    if current_q_idx >= total_q:
                                        st.markdown('<div id="quiz-results"></div>', unsafe_allow_html=True)
                                        st.success(f"🎉 Quiz Complete!")
                                        final_score = st.session_state[f"quiz_score_{sid}"]
                                        percentage = round((final_score / total_q) * 100)
                                    
                                        # Feedback
                                        if percentage >= 90:
                                            feedback = "Excellent work"
                                        elif percentage >= 70:
                                            feedback = "Good progress"
                                        else:
                                            feedback = "Needs review"
                                        st.write(f"**Feedback:** {feedback}")
                                    
                                        # Metrics
                                        col1, col2 = st.columns(2)
                                        with col1:
                                            st.metric("Correct answers", final_score)
                                        with col2:
                                            st.metric("Incorrect answers", total_q - final_score)
                                    
                                        # Strengths vs Weak Areas (computed unconditionally, every render
                                        # of this results screen, so it can both be saved below and shown
                                        # further down regardless of whether this is the first render)
                                        answers = st.session_state[f"quiz_answers_{sid}"]
                                        correct_topics = []
                                        missed_concepts = []
                                        for idx, q in enumerate(quiz_list):
                                            # Correctness is decided once, at submit time (see the Submit
                                            # Answer handler below), and stored alongside the raw answer -
                                            # short answer questions can't be re-judged later by simple
                                            # equality, since a correct free-text answer is rarely worded
                                            # identically to the reference answer.
                                            is_correct = (answers.get(idx) or {}).get("is_correct", False)
                                            topic = get_question_topic(q, fallback_label=f"Question {idx+1}")
                                            if is_correct:
                                                correct_topics.append(topic)
                                            else:
                                                missed_concepts.append(topic)

                                        # Save to history once per completed run
                                        if not st.session_state.get(f"quiz_results_saved_{sid}", False):
                                            history_entry = {
                                                "date": datetime.now().isoformat(),
                                                "score": final_score,
                                                "percentage": percentage,
                                                "total": total_q,
                                                # Deduped, order kept: what the Home page's "Recommended
                                                # Next Step" card suggests reviewing.
                                                "missed_topics": list(dict.fromkeys(missed_concepts)),
                                            }
                                            if "quiz_history" not in note:
                                                note["quiz_history"] = []
                                            note["quiz_history"].append(history_entry)
                                            notes = st.session_state.notes
                                            notes[sid] = note
                                            st.session_state.notes = notes
                                            save_notes(notes)
                                            st.session_state[f"quiz_results_saved_{sid}"] = True

                                            # Only here, at the moment a quiz is really finished, does
                                            # today count as a study day. Then refresh the streak shown
                                            # at the top of the page and in the stats bar.
                                            record_study_day(st.session_state.streak_data)

                                        st.subheader("Strengths vs Weak Areas")
                                        col1, col2 = st.columns(2)
                                        with col1:
                                            st.write("**Correct topics:**")
                                            for t in correct_topics:
                                                st.write(f"- {t}")
                                        with col2:
                                            st.write("**Missed concepts:**")
                                            for t in missed_concepts:
                                                st.write(f"- {t}")
                                    
                                        # Show detailed results
                                        st.subheader("Results Summary")
                                        answers = st.session_state[f"quiz_answers_{sid}"]

                                        for idx, q in enumerate(quiz_list):
                                            record = answers.get(idx) or {}
                                            user_answer = record.get("answer")
                                            is_correct = record.get("is_correct", False)
                                            correct = q.get("correctAnswer") or q.get("correct_answer")
                                            q_type = q.get("type", "multiple_choice")

                                            emoji = "✅" if is_correct else "❌"
                                            with st.expander(f"{emoji} Q{idx+1}: {q['question'][:50]}..."):
                                                st.write(f"**Question:** {q['question']}")
                                                if q_type == "short_answer":
                                                    st.write(f"**Your answer:** {user_answer or 'N/A'}")
                                                    st.write(f"**Reference answer:** {correct}")
                                                    if record.get("feedback"):
                                                        st.write(f"**Feedback:** {record['feedback']}")
                                                else:
                                                    st.write(f"**Your answer:** {user_answer} - {normalize_quiz_sentence(q['choices'].get(user_answer, 'N/A'))}")
                                                    st.write(f"**Correct answer:** {correct} - {normalize_quiz_sentence(q['choices'][correct])}")
                                                    st.write(f"**Explanation:** {build_feedback_explanation(q, user_answer)}")
                                                st.write(f"**Evidence:** {normalize_quiz_sentence(q.get('evidence', ''))}")
                                    
                                        st.write("---")
                                        # Retake button
                                        if st.button("🔄 Retake Quiz", use_container_width=True):
                                            st.session_state[f"quiz_current_{sid}"] = 0
                                            st.session_state[f"quiz_score_{sid}"] = 0
                                            st.session_state[f"quiz_answers_{sid}"] = {}
                                            st.session_state[f"quiz_submitted_{sid}"] = False
                                            st.session_state[f"quiz_results_saved_{sid}"] = False
                                            st.rerun()
                                    else:
                                        # Show current question
                                        q = quiz_list[current_q_idx]
                                        q_type = q.get("type", "multiple_choice")
                                        choice_key = f"quiz_choice_{sid}_{current_q_idx}"
                                        submitted = st.session_state.get(f"quiz_submitted_{sid}", False)
                                        center_left, center_mid, center_right = st.columns([1, 2.8, 1])

                                        section_label = {
                                            "multiple_choice": "Choose the best answer.",
                                            "true_false": "True or False?",
                                            "short_answer": "Type your answer.",
                                        }[q_type]
                                        option_keys = {
                                            "multiple_choice": ["A", "B", "C", "D"],
                                            "true_false": ["True", "False"],
                                        }.get(q_type)

                                        with center_mid:
                                            progress = (current_q_idx) / total_q
                                            st.progress(progress)
                                            st.markdown(
                                                f"""
                                                <div class="quiz-shell">
                                                    <div class="quiz-question-card">
                                                        <div class="quiz-progress-label">Question {current_q_idx + 1} of {total_q}</div>
                                                        <p class="quiz-question-text">{html.escape(q['question'])}</p>
                                                        <div class="quiz-section-label">{section_label}</div>
                                                    </div>
                                                </div>
                                                """,
                                                unsafe_allow_html=True,
                                            )

                                            if submitted:
                                                record = st.session_state[f"quiz_answers_{sid}"].get(current_q_idx) or {}
                                                selected = record.get("answer")
                                                is_correct = record.get("is_correct", False)
                                                correct = q.get("correctAnswer") or q.get("correct_answer")

                                                if q_type == "short_answer":
                                                    render_quiz_feedback_card("Your answer", selected or "(no answer)")
                                                else:
                                                    render_quiz_option_summary(q, selected, option_keys)

                                                if is_correct:
                                                    st.success("✅ Correct.")
                                                elif q_type == "short_answer":
                                                    st.error(f"❌ Not quite. Reference answer: {correct}")
                                                else:
                                                    st.error(f"❌ Not quite. The correct answer is {correct}.")

                                                if q_type == "short_answer":
                                                    render_quiz_feedback_card("Feedback", record.get("feedback") or build_feedback_explanation(q))
                                                else:
                                                    render_quiz_feedback_card("Why this is correct", build_feedback_explanation(q, selected))

                                                next_label = "See Results" if current_q_idx == total_q - 1 else "Next Question →"
                                                if st.button(next_label, key=f"quiz_next_{sid}_{current_q_idx}", use_container_width=True):
                                                    st.session_state[f"quiz_current_{sid}"] += 1
                                                    st.session_state[f"quiz_submitted_{sid}"] = False
                                                    st.session_state.pop(choice_key, None)
                                                    st.rerun()
                                            else:
                                                if q_type == "multiple_choice":
                                                    selected = st.radio(
                                                        "Choose an answer:",
                                                        options=option_keys,
                                                        format_func=lambda x: f"{x}. {q['choices'][x]}",
                                                        key=choice_key,
                                                        label_visibility="collapsed"
                                                    )
                                                elif q_type == "true_false":
                                                    selected = st.radio(
                                                        "Choose an answer:",
                                                        options=option_keys,
                                                        key=choice_key,
                                                        label_visibility="collapsed"
                                                    )
                                                else:
                                                    selected = st.text_area(
                                                        "Your answer:",
                                                        key=choice_key,
                                                        label_visibility="collapsed",
                                                        placeholder="Type your answer here...",
                                                    )

                                                if st.button("Submit Answer", key=f"quiz_submit_{sid}_{current_q_idx}", use_container_width=True):
                                                    correct = q.get("correctAnswer") or q.get("correct_answer")
                                                    if q_type == "short_answer":
                                                        with st.spinner("Checking your answer..."):
                                                            is_correct, feedback = grade_short_answer(q["question"], correct, selected or "")
                                                        st.session_state[f"quiz_answers_{sid}"][current_q_idx] = {
                                                            "answer": selected, "is_correct": is_correct, "feedback": feedback,
                                                        }
                                                    else:
                                                        is_correct = selected == correct
                                                        st.session_state[f"quiz_answers_{sid}"][current_q_idx] = {
                                                            "answer": selected, "is_correct": is_correct,
                                                        }
                                                    if is_correct:
                                                        st.session_state[f"quiz_score_{sid}"] += 1
                                                    st.session_state[f"quiz_submitted_{sid}"] = True
                                                    st.rerun()
                            else:
                                st.write("---")
                                st.write(f"**{len(note['quiz'])} questions ready**")
                                st.write(f"Click the button below to start the quiz!")
                            
                                if st.button("▶️ Start Quiz Now", use_container_width=True):
                                    st.session_state[f"quiz_started_{sid}"] = True
                                    st.session_state[f"quiz_current_{sid}"] = 0
                                    st.session_state[f"quiz_score_{sid}"] = 0
                                    st.session_state[f"quiz_answers_{sid}"] = {}
                                    st.session_state[f"quiz_submitted_{sid}"] = False
                                    st.session_state[f"quiz_results_saved_{sid}"] = False
                                    st.rerun()

                        # ===============================
                        # SECTION: PROGRESS HISTORY
                        # ===============================
                        if note.get("quiz_history") and len(note["quiz_history"]) > 0:
                            if selected_tab == "📊 Progress History":
                                st.subheader("📊 Quiz Progress History")
                                st.write(f"**{len(note['quiz_history'])} attempts recorded**")
                                st.write("---")
                            
                                # Sort by date descending
                                history = sorted(note["quiz_history"], key=lambda x: x["date"], reverse=True)
                            
                                for attempt in history:
                                    date_obj = datetime.fromisoformat(attempt["date"])
                                    formatted_date = date_obj.strftime("%B %d, %Y at %I:%M %p")
                                
                                    with st.expander(f"📅 {formatted_date} - {attempt['score']}/{attempt['total']} ({attempt['percentage']}%)"):
                                        col1, col2 = st.columns(2)
                                        with col1:
                                            st.metric("Score", f"{attempt['score']}/{attempt['total']}")
                                        with col2:
                                            st.metric("Percentage", f"{attempt['percentage']}%")
                    if not note.get("flashcards") and not note.get("quiz"):
                        st.info("👆 Generate Flashcards or Quiz to get started!")
        
            # Back to top button
            st.divider()
            col1, col2, col3 = st.columns([1, 1, 1])
            with col2:
                if "scroll_to_top" not in st.session_state:
                    st.session_state.scroll_to_top = False
                if st.button("⬆️ Back to Top", use_container_width=True):
                    st.session_state.scroll_to_top = True
                if st.session_state.scroll_to_top:
                    components.html("""
                    <script>
                    setTimeout(() => {
                        const el = parent.document.querySelector('#study-top');
                        if (el) el.scrollIntoView({behavior: 'smooth', block: 'start'});
                    }, 400);
                    </script>
                    """, height=0)
                    st.session_state.scroll_to_top = False

            # Scroll to a target section after an action elsewhere on the page
            # (e.g. jumping to the quiz right after it's generated).
            if st.session_state.get("pending_scroll_target"):
                target_id = st.session_state.pop("pending_scroll_target")
                components.html(f"""
                <script>
                setTimeout(() => {{
                    const el = parent.document.querySelector('#{target_id}');
                    if (el) el.scrollIntoView({{behavior: 'smooth', block: 'start'}});
                }}, 400);
                </script>
                """, height=0)


    # ===============================
    # 10. Settings Page
    # ===============================
    elif option == "Settings":
        # ---- page styling: three rounded cards, blue accents, 24px padding, 24px between them ----
        _set_css = """
        <style>
        .stMainBlockContainer { padding-top: 4.6rem !important; padding-bottom: 2rem !important; }
        .stMainBlockContainer > [data-testid="stVerticalBlock"] { gap: 0 !important; }
        .st-key-page_Settings { gap: 24px !important; max-width: 1180px; }

        /* heading */
        .set-hero { position: relative; margin-top: 18px; }
        .set-eyebrow { color: #7fb4ff; font-size: 0.78rem; font-weight: 700; letter-spacing: 0.22em; text-transform: uppercase; margin-bottom: 6px; }
        .st-key-page_Settings .set-h1 { color: #f8fafc !important; font-size: 2.6rem !important; font-weight: 800 !important; letter-spacing: -0.02em; line-height: 1.1 !important; margin: 0 !important; padding: 0 !important; }
        .st-key-page_Settings .set-sub { color: #aab3c2 !important; font-size: 1.2rem !important; margin: 8px 0 0 0 !important; }
        .set-spark { position: absolute; background: #5aa2ff; -webkit-mask: url("__SPARK__") center / contain no-repeat; mask: url("__SPARK__") center / contain no-repeat; filter: drop-shadow(0 0 8px rgba(90,162,255,0.8)); }
        .set-spark.s1 { width: 30px; height: 30px; right: 14%; top: -2px; }
        .set-spark.s2 { width: 20px; height: 20px; right: 11%; top: 38px; }

        /* the three cards */
        .st-key-set_card_study, .st-key-set_card_gen, .st-key-set_card_look {
            border: 1px solid rgba(90, 162, 255, 0.32); border-radius: 18px; padding: 24px !important;
            background: rgba(14, 19, 32, 0.78); gap: 20px !important;
            box-shadow: 0 0 0 1px rgba(90,162,255,0.06), 0 18px 40px -26px rgba(90,162,255,0.45);
        }
        .set-head { display: flex; align-items: center; gap: 16px; }
        .set-ic { flex: none; width: 56px; height: 56px; border-radius: 14px; background: rgba(90,162,255,0.14); border: 1px solid rgba(90,162,255,0.4); position: relative; }
        .set-ic::before { content: ""; position: absolute; inset: 14px; background: #7fb4ff; -webkit-mask: var(--ic) center / contain no-repeat; mask: var(--ic) center / contain no-repeat; }
        .set-ic-book { --ic: url("__BOOK__"); } .set-ic-gen { --ic: url("__SPARKLES__"); } .set-ic-look { --ic: url("__PALETTE__"); }
        .set-title { color: #f8fafc; font-size: 1.45rem; font-weight: 700; line-height: 1.2; }
        .set-desc { color: #aab3c2; font-size: 1rem; margin-top: 2px; }

        /* labels and the divider above each toggle row */
        .st-key-page_Settings [data-testid="stWidgetLabel"] p { color: #e5e9f0 !important; font-size: 1rem !important; font-weight: 500 !important; }
        .set-row-title { color: #f8fafc; font-size: 1.05rem; font-weight: 700; }
        .set-row-sub { color: #aab3c2; font-size: 0.95rem; margin-top: 2px; }
        .st-key-set_toggle_shuffle, .st-key-set_toggle_examples { border-top: 1px solid rgba(255,255,255,0.1); padding-top: 18px; }
        .st-key-settings_shuffle_questions, .st-key-settings_auto_examples { display: flex; justify-content: flex-end; }

        /* Easy / Medium / Hard as one segmented control */
        .st-key-settings_quiz_difficulty { width: 100% !important; }
        .st-key-settings_quiz_difficulty [data-testid="stWidgetLabel"] { display: flex !important; }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] {
            display: grid !important; grid-template-columns: repeat(3, 1fr); gap: 0 !important; column-gap: 0 !important; row-gap: 0 !important; width: 100%;
            border: 1px solid rgba(90,162,255,0.35); border-radius: 12px; overflow: hidden; background: rgba(255,255,255,0.03);
        }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label {
            margin: 0 !important; padding: 11px 0 !important; justify-content: center; border-radius: 0 !important; border: 0 !important; outline: none !important; box-shadow: none !important;
            background: transparent !important; cursor: pointer; transition: background-color 0.2s ease, color 0.2s ease;
        }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label:hover { background: rgba(90,162,255,0.12) !important; }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label:has(input:checked) { background: #5aa2ff !important; }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label > div > div > div:first-child:not([data-testid]) { display: none !important; }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label div,
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label [data-testid="stMarkdownContainer"] { color: #dbe2ee !important; }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label:has(input:checked) div,
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label:has(input:checked) p { color: #ffffff !important; font-weight: 700 !important; }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label > div { width: 100%; }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label > div > div { justify-content: center !important; width: 100%; }
        .st-key-settings_quiz_difficulty div[role="radiogroup"] label p { margin: 0 !important; font-size: 1.02rem !important; }

        /* Light / Dark / System as selectable preview tiles */
        .st-key-settings_theme, .st-key-settings_theme [data-testid="stRadio"] { width: 100% !important; }
        .st-key-settings_theme div[role="radiogroup"] { display: flex !important; gap: 14px; flex-wrap: wrap; justify-content: flex-end; width: 100%; }
        .st-key-settings_theme div[role="radiogroup"] label {
            position: relative; flex: 1 1 130px; max-width: 190px; height: 132px; margin: 0 !important; padding: 0 14px 12px !important;
            display: flex !important; align-items: flex-end; border-radius: 14px; overflow: hidden; cursor: pointer;
            border: 1px solid rgba(255,255,255,0.14); background: rgba(255,255,255,0.04);
            transition: border-color 0.2s ease, box-shadow 0.2s ease, transform 0.2s ease;
        }
        .st-key-settings_theme div[role="radiogroup"] label:hover { border-color: rgba(90,162,255,0.6); transform: translateY(-2px); }
        .st-key-settings_theme div[role="radiogroup"] label:has(input:checked) {
            border: 2px solid #5aa2ff; background: rgba(90,162,255,0.1); box-shadow: 0 0 0 3px rgba(90,162,255,0.2), 0 12px 28px -14px rgba(90,162,255,0.7);
        }
        .st-key-settings_theme div[role="radiogroup"] label:has(input:checked)::after {
            content: "\\2713"; position: absolute; top: 0; right: 0; width: 28px; height: 28px; display: flex; align-items: center; justify-content: center;
            background: #5aa2ff; color: #ffffff; font-weight: 800; font-size: 0.95rem; border-radius: 0 12px 0 12px;
        }
        .st-key-settings_theme div[role="radiogroup"] label div, .st-key-settings_theme div[role="radiogroup"] label [data-testid="stMarkdownContainer"] { color: #e5e9f0 !important; }
        .st-key-settings_theme div[role="radiogroup"] label > div { position: absolute !important; z-index: 1; left: 14px; right: 14px; bottom: 12px; width: auto !important; }
        .st-key-settings_theme div[role="radiogroup"] label > div > div { display: flex !important; align-items: center !important; gap: 8px; }
        .st-key-settings_theme div[role="radiogroup"] label p { margin: 0 !important; font-size: 0.98rem !important; }
        /* the mini window drawn in each tile */
        .st-key-settings_theme div[role="radiogroup"] label::before {
            content: ""; position: absolute; top: 10px; left: 10px; right: 10px; height: 74px; border-radius: 8px;
            background:
                radial-gradient(circle at 9px 8px, #ef4444 2.6px, transparent 3px), radial-gradient(circle at 20px 8px, #f59e0b 2.6px, transparent 3px), radial-gradient(circle at 31px 8px, #22c55e 2.6px, transparent 3px),
                linear-gradient(var(--bar), var(--bar)) 8px 22px / 22px 44px no-repeat,
                linear-gradient(var(--bar), var(--bar)) 38px 26px / 55% 7px no-repeat,
                linear-gradient(var(--bar), var(--bar)) 38px 40px / 40% 7px no-repeat,
                linear-gradient(var(--bar), var(--bar)) 38px 54px / 48% 7px no-repeat,
                var(--win);
            box-shadow: 0 2px 8px rgba(0,0,0,0.35);
        }
        .st-key-settings_theme div[role="radiogroup"] label:nth-of-type(1)::before { --win: #f3f6fb; --bar: #d3dbe9; }
        .st-key-settings_theme div[role="radiogroup"] label:nth-of-type(2)::before { --win: #0f131c; --bar: #2a3346; }
        .st-key-settings_theme div[role="radiogroup"] label:nth-of-type(3)::before {
            background:
                radial-gradient(circle at 9px 8px, #ef4444 2.6px, transparent 3px), radial-gradient(circle at 20px 8px, #f59e0b 2.6px, transparent 3px), radial-gradient(circle at 31px 8px, #22c55e 2.6px, transparent 3px),
                linear-gradient(#d3dbe9, #d3dbe9) 8px 22px / 22px 44px no-repeat,
                linear-gradient(#d3dbe9, #d3dbe9) 38px 26px / 30% 7px no-repeat,
                linear-gradient(#2a3346, #2a3346) calc(100% - 10px) 40px / 30% 7px no-repeat,
                linear-gradient(#2a3346, #2a3346) calc(100% - 10px) 54px / 26% 7px no-repeat,
                linear-gradient(90deg, #f3f6fb 50%, #0f131c 50%);
        }
        .st-key-settings_theme div[role="radiogroup"] label > div > div > div:first-child:not([data-testid]) { border-color: rgba(255,255,255,0.5) !important; background: transparent !important; }
        .st-key-settings_theme div[role="radiogroup"] label:has(input:checked) > div > div > div:first-child:not([data-testid]) { border-color: #5aa2ff !important; background: #5aa2ff !important; }

        /* the toggles, in the app blue */
        .st-key-settings_shuffle_questions, .st-key-settings_auto_examples { width: 100% !important; }
        .st-key-settings_shuffle_questions label > div:first-of-type, .st-key-settings_auto_examples label > div:first-of-type { margin-right: 0 !important; }
        .st-key-settings_shuffle_questions label:has(input:checked) > div:first-of-type, .st-key-settings_auto_examples label:has(input:checked) > div:first-of-type { background: #5aa2ff !important; }
        .st-key-set_toggle_shuffle [data-testid="stHorizontalBlock"], .st-key-set_toggle_examples [data-testid="stHorizontalBlock"] { flex-wrap: nowrap !important; }
        .st-key-set_toggle_shuffle [data-testid="stColumn"], .st-key-set_toggle_examples [data-testid="stColumn"] { min-width: 0 !important; }
        .st-key-set_toggle_shuffle [data-testid="stColumn"]:last-child, .st-key-set_toggle_examples [data-testid="stColumn"]:last-child { flex: 0 0 64px !important; width: 64px !important; }
        .st-key-set_toggle_shuffle [data-testid="stColumn"]:first-child, .st-key-set_toggle_examples [data-testid="stColumn"]:first-child { flex: 1 1 auto !important; width: auto !important; }
        .st-key-settings_shuffle_questions label:not(:has(input:checked)) > div:first-of-type, .st-key-settings_auto_examples label:not(:has(input:checked)) > div:first-of-type { background: rgba(255,255,255,0.22) !important; }
        /* multiselect chip in the app blue */
        .st-key-settings_question_types [data-tag] { background: rgba(90,162,255,0.2) !important; border: 1px solid rgba(90,162,255,0.55); }
        .st-key-settings_question_types [data-tag] span, .st-key-settings_question_types [data-tag] svg { color: #cfe3ff !important; }

        /* Save Settings: solid blue, on the right */
        .st-key-settings_save { display: flex; justify-content: flex-end; }
        .st-key-settings_save button[data-testid] {
            background: #5aa2ff !important; border: 1px solid #5aa2ff !important; color: #ffffff !important; font-weight: 700 !important;
            min-height: 52px !important; border-radius: 14px !important; gap: 10px; justify-content: center !important;
        }
        .st-key-settings_save button > div { flex: none !important; width: auto !important; }
        .st-key-settings_save button p { color: #ffffff !important; font-size: 1.1rem !important; margin: 0 !important; }
        .st-key-settings_save button::before { content: ""; width: 20px; height: 20px; background: currentColor; -webkit-mask: url("__SAVE__") center / contain no-repeat; mask: url("__SAVE__") center / contain no-repeat; }
        @media (max-width: 760px) {
            .st-key-page_Settings .set-h1 { font-size: 2rem !important; }
            .set-spark { display: none; }
            .st-key-settings_theme div[role="radiogroup"] { justify-content: flex-start; }
        }
        </style>
        """
        for _tag, _inner in {
            "__SPARK__": '<path d="M12 2l1.9 7.1L21 11l-7.1 1.9L12 20l-1.9-7.1L3 11l7.1-1.9z" fill="#000" stroke="none"/>',
            "__BOOK__": '<path d="M2 3h6a4 4 0 0 1 4 4v14a3 3 0 0 0-3-3H2z"/><path d="M22 3h-6a4 4 0 0 0-4 4v14a3 3 0 0 1 3-3h7z"/>',
            "__SPARKLES__": '<path d="m12 3-1.912 5.813a2 2 0 0 1-1.275 1.275L3 12l5.813 1.912a2 2 0 0 1 1.275 1.275L12 21l1.912-5.813a2 2 0 0 1 1.275-1.275L21 12l-5.813-1.912a2 2 0 0 1-1.275-1.275L12 3Z"/><path d="M5 3v4"/><path d="M19 17v4"/><path d="M3 5h4"/><path d="M17 19h4"/>',
            "__PALETTE__": '<circle cx="13.5" cy="6.5" r="1"/><circle cx="17.5" cy="10.5" r="1"/><circle cx="8.5" cy="7.5" r="1"/><circle cx="6.5" cy="12.5" r="1"/><path d="M12 2C6.5 2 2 6.5 2 12s4.5 10 10 10c.926 0 1.648-.746 1.648-1.688 0-.437-.18-.835-.437-1.125-.29-.289-.438-.652-.438-1.125a1.64 1.64 0 0 1 1.668-1.668h1.996c3.051 0 5.555-2.503 5.555-5.554C21.965 6.012 17.461 2 12 2z"/>',
            "__SAVE__": '<path d="M15.2 3a2 2 0 0 1 1.4.6l3.8 3.8a2 2 0 0 1 .6 1.4V19a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2z"/><path d="M17 21v-7a1 1 0 0 0-1-1H8a1 1 0 0 0-1 1v7"/><path d="M7 3v4a1 1 0 0 0 1 1h7"/>',
        }.items():
            _set_css = _set_css.replace(_tag, _sb_icon(_inner))
        st.markdown(
            _set_css +
            "<div class='set-hero'><div class='set-eyebrow'>Settings</div>"
            "<div class='set-h1'>Make NexLearn yours</div>"
            "<div class='set-sub'>Your study style. Your settings.</div>"
            "<span class='set-spark s1'></span><span class='set-spark s2'></span></div>",
            unsafe_allow_html=True,
        )

        current = st.session_state.settings

        def _set_head(icon_cls, title, desc):
            return (
                f"<div class='set-head'><div class='set-ic {icon_cls}'></div>"
                f"<div><div class='set-title'>{title}</div><div class='set-desc'>{desc}</div></div></div>"
            )

        # ---- Study preferences ----
        with st.container(key="set_card_study"):
            st.markdown(_set_head("set-ic-book", "Study preferences", "Set your default practice options."), unsafe_allow_html=True)
            col_a, col_b = st.columns(2, gap="large")
            with col_a:
                quiz_difficulty = st.radio(
                    "Default quiz difficulty", QUIZ_DIFFICULTIES,
                    index=QUIZ_DIFFICULTIES.index(current["quiz_difficulty"]), horizontal=True, key="settings_quiz_difficulty",
                )
            with col_b:
                quiz_question_count = st.selectbox(
                    "Quiz questions", QUESTION_COUNT_OPTIONS,
                    index=QUESTION_COUNT_OPTIONS.index(current["quiz_question_count"]), key="settings_quiz_question_count",
                )
            col_c, col_d = st.columns(2, gap="large")
            with col_c:
                flashcard_count = st.selectbox(
                    "Flashcards", FLASHCARD_COUNT_OPTIONS,
                    index=FLASHCARD_COUNT_OPTIONS.index(current["flashcard_count"]), key="settings_flashcard_count",
                )
            with col_d:
                question_types = st.multiselect(
                    "Preferred question types", QUESTION_TYPE_OPTIONS,
                    default=current["question_types"], key="settings_question_types",
                    help="Quizzes will mix questions from whichever types you select here.",
                )
            with st.container(key="set_toggle_shuffle"):
                text_col, switch_col = st.columns([6, 1], vertical_alignment="center")
                with text_col:
                    st.markdown(
                        "<div class='set-row-title'>Shuffle questions</div>"
                        "<div class='set-row-sub'>Mix the question order for each quiz.</div>",
                        unsafe_allow_html=True,
                    )
                with switch_col:
                    shuffle_questions = st.toggle(
                        "Shuffle Questions", value=current["shuffle_questions"], key="settings_shuffle_questions",
                        label_visibility="collapsed",
                    )

        # ---- Generation preferences ----
        with st.container(key="set_card_gen"):
            st.markdown(_set_head("set-ic-gen", "Generation preferences", "Set your default explanation options."), unsafe_allow_html=True)
            col_e, col_f = st.columns(2, gap="large")
            with col_e:
                explanation_level = st.selectbox(
                    "Explanation level", EXPLANATION_LEVELS,
                    index=EXPLANATION_LEVELS.index(current["explanation_level"]), key="settings_explanation_level",
                    help="Controls how simple or technical quiz/flashcard explanations are written.",
                )
            with col_f:
                answer_length = st.selectbox(
                    "Answer length", ANSWER_LENGTHS,
                    index=ANSWER_LENGTHS.index(current["answer_length"]), key="settings_answer_length",
                )
            with st.container(key="set_toggle_examples"):
                text_col, switch_col = st.columns([6, 1], vertical_alignment="center")
                with text_col:
                    st.markdown(
                        "<div class='set-row-title'>Automatically generate examples</div>"
                        "<div class='set-row-sub'>Include a brief concrete example in flashcard answers where it helps understanding.</div>",
                        unsafe_allow_html=True,
                    )
                with switch_col:
                    auto_examples = st.toggle(
                        "Automatically Generate Examples", value=current["auto_examples"], key="settings_auto_examples",
                        label_visibility="collapsed",
                    )

        # ---- Appearance ----
        with st.container(key="set_card_look"):
            look_text, look_tiles = st.columns([5, 7], gap="large", vertical_alignment="center")
            with look_text:
                st.markdown(
                    _set_head("set-ic-look", "Appearance", "Customize how NexLearn looks on your device.")
                    + "<div class='set-row-title' style='margin-top:18px'>Theme</div>"
                    "<div class='set-row-sub'>Choose how NexLearn looks on your device.</div>",
                    unsafe_allow_html=True,
                )
            with look_tiles:
                theme = st.radio(
                    "Theme", THEME_OPTIONS,
                    index=THEME_OPTIONS.index(current["theme"]), horizontal=True, key="settings_theme",
                                        label_visibility="collapsed",
                )

        # ---- Saved automatically the moment anything changes (there is no Save button) ----
        _chosen = {
            "quiz_difficulty": quiz_difficulty,
            "quiz_question_count": quiz_question_count,
            "flashcard_count": flashcard_count,
            "question_types": question_types,
            "shuffle_questions": shuffle_questions,
            "explanation_level": explanation_level,
            "answer_length": answer_length,
            "auto_examples": auto_examples,
            "theme": theme,
        }
        if any(current.get(k) != v for k, v in _chosen.items()):
            if not question_types:
                st.error("Select at least one preferred question type - your changes will be saved once you do.")
            else:
                new_settings = dict(current)
                new_settings.update(_chosen)
                st.session_state.settings = new_settings
                save_settings(new_settings)

