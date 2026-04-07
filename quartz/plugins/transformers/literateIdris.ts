import { QuartzTransformerPlugin } from "../types"
import { visit } from "unist-util-visit"
import { Element, Root } from "hast"
import { Plugin } from "unified"

// Fenced block types used in the literate Idris source files
const MATH_BLOCK_TYPES = ["definition", "proposition", "lemma", "theorem", "postulate"] as const

// TikZJax script — renders TikZ/tikz-cd diagrams client-side via WebAssembly
const TIKZJAX_SRC = "https://tikzjax.com/v1/tikzjax.js"

/**
 * rehype plugin: finds <pre><code class="language-tikz"> nodes produced by the
 * markdown fenced-code parser and replaces them with a <figure> containing a
 * <script type="text/tikz"> element.
 *
 * We do this as a rehype (HTML AST) plugin rather than in textTransform so that
 * the tikz content is kept as a raw hast text node and never HTML-encoded.
 * If we inject raw `<script>` HTML in textTransform the unified serializer
 * encodes `&` → `&amp;` and `"` → `&quot;` inside the tag, breaking tikz-cd
 * which uses both as column separators and label delimiters.
 */
const rehypeTikz: Plugin<[], Root> = () => (tree) => {
  visit(tree, "element", (node: Element, index, parent) => {
    if (
      node.tagName !== "pre" ||
      !parent ||
      index === undefined ||
      index === null
    )
      return

    const code = node.children[0]
    if (
      code?.type !== "element" ||
      (code as Element).tagName !== "code"
    )
      return

    const codeEl = code as Element
    const cls = (codeEl.properties?.className as string[]) ?? []
    if (!cls.includes("language-tikz")) return

    // Raw tikz source (the markdown parser leaves it as a text node)
    const rawText = codeEl.children
      .filter((c) => c.type === "text")
      .map((c) => (c as { type: "text"; value: string }).value)
      .join("")

    // Extract caption from data attributes set by remark-gfm meta parsing
    // (the `{caption="..."}` part of ```tikz {caption="..."})
    const meta: string = (node.data as { meta?: string })?.meta ?? ""
    const captionMatch = meta.match(/caption="([^"]*)"/)
    const caption = captionMatch ? captionMatch[1] : null

    // Strip LaTeX document boilerplate that TikZJax doesn't need
    const tikzContent = rawText
      .replace(/\\usepackage\{[^}]*\}\n?/g, "")
      .replace(/\\begin\{document\}\n?/g, "")
      .replace(/\\end\{document\}\n?/g, "")
      .trim()

    // Build the replacement <figure> node.
    // The <script> text node is intentionally a raw hast text node so that
    // hast-util-to-html writes it verbatim (no HTML encoding).
    const figureChildren: Element["children"] = [
      {
        type: "element",
        tagName: "script",
        properties: { type: "text/tikz" },
        // hast serialises text children of <script> as raw text — no encoding
        children: [{ type: "text", value: tikzContent }],
      },
    ]

    if (caption) {
      figureChildren.push({
        type: "element",
        tagName: "figcaption",
        properties: {},
        children: [{ type: "text", value: caption }],
      })
    }

    const figure: Element = {
      type: "element",
      tagName: "figure",
      properties: { className: ["tikz-figure"] },
      children: figureChildren,
    }

    ;(parent.children as Element["children"])[index] = figure
  })
}

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

      // 3a. Quadruple-backtick form (may contain inner ``` code blocks).
      //     Optional {label=...} attribute is accepted and discarded.
      src = src.replace(
        new RegExp(`\`\`\`\`(${typePattern})(\\s+\\{[^}]*\\})?\\n([\\s\\S]*?)\`\`\`\``, "g"),
        (_match, type: string, _attrs: string, content: string) => toCallout(_match, type, content),
      )

      // 3b. Triple-backtick form with optional {attributes} (prose only)
      src = src.replace(
        new RegExp(`\`\`\`(${typePattern})(\\s+\\{[^}]*\\})?\\n([\\s\\S]*?)\`\`\``, "g"),
        (_match, type: string, _attrs: string, content: string) => toCallout(_match, type, content),
      )

      // 4. Remap `idris` language tag to `haskell` for syntax highlighting.
      //    shiki (used by rehype-pretty-code) does not include an Idris grammar.
      //    Haskell shares enough syntax that highlighting is useful rather than absent.
      src = src.replace(/```idris(\s)/g, "```haskell$1")

      return src
    },
    htmlPlugins() {
      // 4. Replace ```tikz``` fenced blocks with TikZJax <script> elements.
      //    Done as a rehype plugin (not textTransform) to keep LaTeX content as
      //    raw text nodes, preventing the HTML serializer from encoding & and ".
      return [rehypeTikz]
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
