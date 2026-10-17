# NexLearn folders (frontend)

React + TypeScript + Tailwind CSS 4 + shadcn layout (`components.json`, `src/components/ui`, `@/` alias).
The component is `src/components/ui/glass-folder-cards.tsx`; `src/components/glass-folder-cards-demo.tsx` is the demo;
`src/index.tsx` is the bridge that mounts it inside Streamlit (Custom Component v2).

Rebuild after changing anything in `src/` (Node.js 24 is in `.tools/`, kept out of git):

    cd frontend
    .tools\node-v24.22.0-win-x64\npm.cmd run build     # or `npm run build` if Node is on your PATH

That writes `dist/nexlearn-folders.js` and `.css`, which `nexlearn_folders.py` loads. Running the app needs no Node.

