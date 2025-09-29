#import "@preview/theorion:0.4.0": *
#import cosmos.rainbow: *

#let styling(
  course_name: "",
  course_code: "",
  title_size: 30pt,
  title_space: 0em,

  margin: 0.5cm, // 0.5 for computer, 0.1 for phone (cm)
  width: 11cm, // 16 for computer, 8 for phone (cm)
  height: 100cm,
  size: 12pt,

  doc
) = {
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
  // pagebreak() // Pagebreak before heading 1, useful when height is auto
  set text(size: 20pt)
  it
}
show heading.where(level: 2): it =>{
  set text(size: 14pt)
  smallcaps(it)
}
show heading.where(level: 3): it =>{
  set text(size: 12pt)
  it
}
show heading.where(level: 4): it =>{
  it
}

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

set text(
  size: size,
  font: "New Computer Modern",
  lang: "en",
  region: "SE"
)
set par(
  leading: 0.80em
)
set page(
  margin: margin,
  height: height, // auto produces infinite page
  width: width 
)
set terms(
  separator: " "
)
set enum(
  numbering: "(i)"
)
show image: it => align(center, it)

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
make_title(course_name, course_code)

outline(depth: 3)

doc
}