import { Components, Jsx, toJsxRuntime } from "hast-util-to-jsx-runtime"
import { Node, Root } from "hast"
import { Fragment, jsx, jsxs } from "preact/jsx-runtime"
import { trace } from "./trace"
import { type FilePath } from "./path"

const customComponents: Components = {
  table: (props) => (
    <div class="table-container">
      <table {...props} />
    </div>
  ),
  // hast-util-to-jsx-runtime passes script text as JSX children, and Preact's
  // renderer HTML-escapes all text children — turning & into &amp; etc.
  // For TikZJax scripts the content is LaTeX (tikz-cd uses & and " heavily),
  // so we bypass escaping with dangerouslySetInnerHTML.
  script: ({ children, ...props }) => {
    if (props.type === "text/tikz") {
      const raw = Array.isArray(children) ? children.join("") : String(children ?? "")
      return <script {...props} dangerouslySetInnerHTML={{ __html: raw }} />
    }
    return <script {...props}>{children}</script>
  },
}

export function htmlToJsx(fp: FilePath, tree: Node) {
  try {
    return toJsxRuntime(tree as Root, {
      Fragment,
      jsx: jsx as Jsx,
      jsxs: jsxs as Jsx,
      elementAttributeNameCase: "html",
      components: customComponents,
    })
  } catch (e) {
    trace(`Failed to parse Markdown in \`${fp}\` into JSX`, e as Error)
  }
}
