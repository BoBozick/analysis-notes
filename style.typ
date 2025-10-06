#import "@preview/theorion:0.4.0": *
#import cosmos.rainbow: *

#let styling(
  course_name: "",
  course_code: "",
  title_size: 30pt,
  title_space: 0em,

  size: 12pt,
  margin: 0.5cm, // 0.5 for computer, 0.1 for phone (cm)
  width: 11cm,   // 16 for computer, 8 for phone (cm)
  height: auto,
  heading_break: false,
  contents: false,

  doc
) = {
  // Headings
  set heading(
    numbering: (..levels) => {
      if levels.pos().len() <= 3 {
        levels.pos().map(str).join(".") + "."
      } else {
        "---"
      }
    }
  )

  show heading.where(level: 1): it =>{
    if heading_break and not it.body == [Contents] {
      pagebreak()
    }
    set text(size: size + 8pt)
    it
  }
  show heading.where(level: 2): it =>{
    set text(size: size + 2pt)
    smallcaps(it)
  }
  show heading.where(level: 3): it =>{
    set text(size: size)
    it
  }
  show heading.where(level: 4): set heading(
    outlined: false
  )

  let make_title(course_name, course_code) = {
    if course_name != "" {
      align(center, {
        v(0em)
        text(size: title_size, course_name)
        v(-2em)
        text(size: 16pt, course_code)
        v(title_space)
        }
      )
    }
  }

  // Outline
  show outline.entry: it => link(
    it.element.location(),
    // Drop the fill and the page.
    it.indented(it.prefix(), it.body()),
  )
  show outline.entry.where(
    level: 1
  ): set text(weight: "bold")
  show outline.entry.where(
    level: 2
  ): smallcaps

  // Text
  set text(
    size: size,
    font: "New Computer Modern",
    lang: "en",
    region: "SE",
  )
  set terms(
    separator: " "
  )
  set enum(
    numbering: "(i)"
  )

  // Layout
  set par(
    leading: 0.80em,
  )
  set page(
    margin: margin,
    height: height,
    width: width,
  )

  show image: it => align(center, it)

  // Make document
  make_title(course_name, course_code)
  if contents {outline()}
  doc
}

#let (corollary-counter, corollary-box, corollary, show-corollary) = make-frame(
  "corollary",
  theorion-i18n-map.at("corollary"),
  counter: theorem-counter,
  render: render-fn.with(fill: red.darken(20%)),
  )