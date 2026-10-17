import path from "node:path"
import { defineConfig } from "vite"
import react from "@vitejs/plugin-react"
import tailwindcss from "@tailwindcss/vite"

// Builds the folder component into two plain files Streamlit can load:
//   dist/nexlearn-folders.js   (one ES module, React included)
//   dist/nexlearn-folders.css  (Tailwind + the shadcn tokens)
export default defineConfig({
  plugins: [react(), tailwindcss()],
  resolve: { alias: { "@": path.resolve(import.meta.dirname, "src") } },
  define: { "process.env.NODE_ENV": JSON.stringify("production") },
  build: {
    outDir: "dist",
    emptyOutDir: true,
    cssCodeSplit: false,
    minify: true,
    lib: {
      entry: path.resolve(import.meta.dirname, "src/index.tsx"),
      formats: ["es"],
      fileName: () => "nexlearn-folders.js",
      cssFileName: "nexlearn-folders",
    },
  },
})
