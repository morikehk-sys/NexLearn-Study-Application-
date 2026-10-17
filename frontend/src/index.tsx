import * as React from "react"
import { createRoot, type Root } from "react-dom/client"
import type { FrontendRenderer, FrontendRendererArgs } from "@streamlit/component-v2-lib"
import GlassFolder, { type FolderFile, type FolderArt } from "@/components/ui/glass-folder-cards"
import "./index.css"

/** What Python sends (see nexlearn_folders.py). */
type FolderSpec = {
  id: string
  label: string
  meta?: string
  tone?: "light" | "dark"
  art?: FolderArt
  seed?: number
  action?: "add" | "more" | "none"
  labelPlacement?: "bottom-left" | "top-left" | "top-right"
  files: FolderFile[]
}
type Data = { folders: FolderSpec[]; width?: number }
type TriggerKeys = { file: { folder: string; name: string; index: number } }

// one React root per mounted instance, so several components on a page never clash
const roots = new WeakMap<Element, Root>()

const renderer: FrontendRenderer<Record<string, never>, Data> = (args: FrontendRendererArgs<Record<string, never>, Data>) => {
  const { data, parentElement } = args
  const setTriggerValue = args.setTriggerValue as unknown as <K extends keyof TriggerKeys>(key: K, value: TriggerKeys[K]) => void

  let mount = parentElement.querySelector<HTMLElement>("[data-nexlearn-folders]")
  if (!mount) {
    mount = document.createElement("div")
    mount.setAttribute("data-nexlearn-folders", "")
    parentElement.appendChild(mount)
  }
  let root = roots.get(mount)
  if (!root) {
    root = createRoot(mount)
    roots.set(mount, root)
  }

  const folders = data?.folders ?? []
  root.render(
    <div className="flex w-full flex-wrap items-end justify-center gap-x-14 gap-y-10 py-4">
      {folders.map((f, i) => (
        <GlassFolder
          key={f.id}
          label={f.label}
          meta={f.meta}
          tone={f.tone ?? "dark"}
          art={f.art ?? "none"}
          seed={f.seed ?? 3}
          action={f.action ?? "none"}
          labelPlacement={f.labelPlacement}
          files={f.files}
          width={data?.width ?? 340}
          appearDelay={i * 140}
          onFileSelect={(file, index) => setTriggerValue("file", { folder: f.id, name: file.name, index })}
        />
      ))}
    </div>,
  )

  return () => {
    const r = roots.get(mount!)
    roots.delete(mount!)
    // unmount after the current render pass so React is never torn down mid-update
    setTimeout(() => r?.unmount(), 0)
  }
}

export default renderer
