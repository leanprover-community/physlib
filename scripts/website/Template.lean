/-

Modified from:

https://github.com/leanprover/doc-gen4/blob/main/DocGen4/Output/Template.lean

Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving

Modifications include: Style changes.

Test these changes with (doc-gen4 is a dependency of the nested `docs/build` project, not of
Physlib, see `docs/build/lakefile.toml`):
- (cd docs/build && lake build Physlib.Meta.Basic:docs) to fetch and build doc-gen4
- cp ./scripts/website/Template.lean .lake/packages/doc-gen4/DocGen4/Output/Template.lean
- (cd docs/build && lake build Physlib.Meta.Basic:docs)
- (cd docs/build/.lake/build/doc && python3 -m http.server)

-/
import DocGen4.Output.ToHtmlFormat
import DocGen4.Output.Navbar

namespace DocGen4
namespace Output

open scoped DocGen4.Jsx

/--
The HTML template used for all pages.
-/
def baseHtmlGenerator (title : String) (site : Array Html) : BaseHtmlM Html := do
  let moduleConstant :=
    if let some module := ← getCurrentName then
      #[<script>{.raw s!"const MODULE_NAME={String.quote module.toString};"}</script>]
    else
      #[]
  pure
    <html lang="en">
      <head>
        [← baseHtmlHeadDeclarations]

        <title>{title}</title>
        <script defer="true" src={s!"{← getRoot}mathjax-config.js"}></script>
        <script defer="true" src="https://cdnjs.cloudflare.com/polyfill/v3/polyfill.min.js?features=es6"></script>
        <script defer="true" src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>

        <script>{.raw s!"const SITE_ROOT={String.quote (← getRoot)};"}</script>
        [moduleConstant]
        <script type="module" src={s!"{← getRoot}jump-src.js"}></script>
        <script type="module" src={s!"{← getRoot}search.js"}></script>
        <script type="module" src={s!"{← getRoot}expand-nav.js"}></script>
        <script type="module" src={s!"{← getRoot}how-about.js"}></script>
        <script type="module" src={s!"{← getRoot}instances.js"}></script>
        <script type="module" src={s!"{← getRoot}importedBy.js"}></script>
      </head>

      <body>

        <input id="nav_toggle" type="checkbox"/>

        <header style="background-color: #2C3E50; color: #fff;">
          <h1><label for="nav_toggle"></label><span>
          <a href="physlib.io" style="color: #fff; text-decoration: none; font-family: serif">
          Physlib Documentation</a>
          </span></h1>
          <h2  style="color: #fff; font-family: serif">[breakWithin title]</h2>
          <form action="https://google.com/search" method="get" id="search_form" style="color: var(--text-color);">
            <input type="hidden" name="sitesearch" value="https://leanprover-community.github.io/mathlib4_docs"/>
            <input type="text" name="q" autocomplete="off"/>{.raw "&#32;"}
            <button id="search_button" onclick={s!"javascript: form.action='{← getRoot}search.html';"}>Search</button>
            <button>Google site search</button>
          </form>
        </header>

        [site]

        <nav class="nav">
          <iframe src={s!"{← getRoot}navbar.html"} class="navframe" frameBorder="0"></iframe>
        </nav>
      </body>
    </html>

/--
A comfortability wrapper around `baseHtmlGenerator`.
-/
def baseHtml (title : String) (site : Html) : BaseHtmlM Html := baseHtmlGenerator title #[site]

end Output
end DocGen4
