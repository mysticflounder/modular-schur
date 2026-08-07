# Applying a design to the status page

`template.html` is a pandoc template, not a finished page. `scripts/build-site.sh`
fills its slots with the content from `site/content/index.md` and writes
`docs/index.html`, which GitHub Pages serves.

## Applying a Claude Design page

1. Put the design's full HTML in `template.html`.
2. Put its CSS in `style.css` rather than inlining it in the template, so design
   and structure can be updated independently.
3. Re-insert the slots listed below.
4. Run `scripts/build-site.sh --serve` and check the result at
   `http://localhost:8000`.

## Slots

| Slot | Required | Where |
| --- | --- | --- |
| `$title$` | yes | `<title>` and the page header |
| `$math$` | yes | inside `<head>` — pandoc emits the KaTeX `<link>` and `<script>` here |
| `$body$` | yes | the rendered content, inside `<main>` |
| `$toc$` | no | section nav; wrap in `$if(toc)$ … $endif$` |
| `$subtitle$`, `$updated$`, `$repo$` | no | set in `scripts/build-site.sh` |

## Two rules that will bite

**Every `$` in the template is template syntax**, including inside HTML
comments, `<style>` blocks, and `<script>` blocks. A literal dollar sign must be
written `$$`. This is why the seam documentation lives in this file instead of
in a comment at the bottom of the template — pandoc was expanding it and
shipping the expansion into the page.

**Asset paths are relative to `docs/`**, not to `site/theme/`: the stylesheet is
at `assets/style.css` and KaTeX under `assets/katex/`. The build copies both
into place.

## Hooks a replacement stylesheet must cover

- From the template: `.page-header`, `.subtitle`, `.updated`, `.toc`,
  `.content`, `.page-footer`
- From pandoc: `section.level1` / `section.level2`, `table`/`th`/`td`,
  `pre`/`code`, `blockquote`
- From KaTeX: `.katex`, `.katex-display` — keep `.katex-display` horizontally
  scrollable or wide equations will overflow on narrow screens

Status labels in the content are plain `<strong>` at the start of a paragraph or
list item, so a design that wants badges should target
`.content li > strong:first-child` and `.content p > strong:first-child`.

## KaTeX

`vendor/katex/` is KaTeX 0.18.1, vendored so the published page has no CDN
dependency. pandoc 3.10 renders math with an inline `katex.render` loop rather
than `auto-render.js`, so only `katex.min.js`, `katex.min.css`, and `fonts/` are
needed. To update, `npm pack katex@latest` and replace the directory contents.
