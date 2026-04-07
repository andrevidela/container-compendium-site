import { QuartzTransformerPlugin } from "../types"

// Fenced block types used in the literate Idris source files
const MATH_BLOCK_TYPES = ["definition", "proposition", "lemma", "theorem", "postulate"] as const

// TikZJax script — renders TikZ/tikz-cd diagrams client-side via WebAssembly
const TIKZJAX_SRC = "https://tikzjax.com/v1/tikzjax.js"

/**
 * Transforms literate Idris markdown files (.idr.md) for web publishing:
 *
 * 1. Strips `<!-- idris ... -->` comment blocks (compiler-only code, not for display)
 * 2. Strips ```idris {hidden=...} ... ``` blocks (visibility modifiers like `public export`)
 * 3. Converts ````definition/lemma/proposition/theorem/postulate ... ```` fences
 *    into Obsidian-style callouts that Quartz renders as styled boxes
 * 4. Converts ```tikz ... ``` blocks into <script type="text/tikz"> elements rendered
 *    by TikZJax, with an optional <figcaption> from the {caption=...} attribute
 * 5. Remaps `idris` language identifier to `haskell` for syntax highlighting
 *    (shiki does not bundle an Idris grammar; Haskell is syntactically close)
 */
export const LiterateIdris: QuartzTransformerPlugin = () => {
  return {
    name: "LiterateIdris",
    textTransform(_ctx, src) {
      // 1. Remove <!-- idris ... --> comment blocks
      //    These wrap Idris module headers and `public export` qualifiers that the
      //    Idris compiler needs but that should not appear on the web page.
      src = src.replace(/<!--\s*idris\s*\n[\s\S]*?-->/g, "")

      // 2. Remove ```idris {hidden=...} ... ``` blocks
      //    These are used to inject compiler-only declarations (e.g. `public export`)
      //    between visible blocks without showing them to readers.
      src = src.replace(/```idris\s+\{[^}]*\}[\s\S]*?```/g, "")

      // 3. Convert math-type fenced blocks into Obsidian callouts.
      //    Two fence styles are used in the source:
      //
      //    a) Quadruple-backtick outer fence (content may contain code blocks):
      //         ````definition
      //         text and ```idris ... ``` inner blocks
      //         ````
      //
      //    b) Triple-backtick with type as language tag (prose-only content,
      //       sometimes with a LaTeX {label=...} attribute that we drop):
      //         ```definition {label="def:category"}
      //         prose text with $math$
      //         ```
      //
      //    Both become:
      //      > [!definition]
      //      > content...
      const typePattern = MATH_BLOCK_TYPES.join("|")

      const toCallout = (_match: string, type: string, content: string) => {
        // Trim trailing newline from content, then add one after the closing
        // blockquote so consecutive blocks are separated by a blank line.
        // Without this, adjacent callouts merge into a single blockquote.
        const trimmed = content.replace(/\n$/, "")
        const quotedContent = trimmed
          .split("\n")
          .map((line) => `> ${line}`)
          .join("\n")
        return `> [!${type}]\n${quotedContent}\n`
      }

      // 3a. Quadruple-backtick form (may contain inner ``` code blocks)
      src = src.replace(new RegExp(`\`\`\`\`(${typePattern})\\n([\\s\\S]*?)\`\`\`\``, "g"), toCallout)

      // 3b. Triple-backtick form with optional {attributes} (prose only)
      src = src.replace(
        new RegExp(`\`\`\`(${typePattern})(\\s+\\{[^}]*\\})?\\n([\\s\\S]*?)\`\`\``, "g"),
        (_match, type: string, _attrs: string, content: string) => toCallout(_match, type, content),
      )

      // 4. Convert ```tikz {caption="..."} ... ``` blocks into TikZJax elements.
      //    TikZJax renders TikZ/tikz-cd diagrams in the browser via WebAssembly.
      //    The LaTeX preamble boilerplate (\usepackage, \begin{document}, etc.) is
      //    stripped; only the body content (tikzcd environments etc.) is kept.
      src = src.replace(
        /```tikz(\s+\{([^}]*)\})?\n([\s\S]*?)```/g,
        (_match, _attrBlock: string, attrs: string, body: string) => {
          // Extract caption="..." from the attribute string if present
          const captionMatch = attrs?.match(/caption="([^"]*)"/)
          const caption = captionMatch ? captionMatch[1] : null

          // Strip LaTeX document boilerplate that TikZJax doesn't need
          const tikzContent = body
            .replace(/\\usepackage\{[^}]*\}\n?/g, "")
            .replace(/\\begin\{document\}\n?/g, "")
            .replace(/\\end\{document\}\n?/g, "")
            .trim()

          const figcaption = caption ? `\n<figcaption>${caption}</figcaption>` : ""
          return `\n<figure class="tikz-figure">\n<script type="text/tikz">\n${tikzContent}\n</script>${figcaption}\n</figure>\n`
        },
      )

      // 5. Remap `idris` language tag to `haskell` for syntax highlighting.
      //    shiki (used by rehype-pretty-code) does not include an Idris grammar.
      //    Haskell shares enough syntax that highlighting is useful rather than absent.
      src = src.replace(/```idris(\s)/g, "```haskell$1")

      return src
    },
    externalResources() {
      return {
        js: [
          {
            src: TIKZJAX_SRC,
            loadTime: "afterDOMReady",
            contentType: "external",
          },
        ],
      }
    },
  }
}
