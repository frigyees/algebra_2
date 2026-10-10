// House style. Changes here affect every fragment; rebuild main.typ after editing.

#let accent = rgb("#2B4C7E")
#let accent-dark = accent.darken(35%)
#let rule-colour = rgb("#B8C4D6")
#let missing-colour = rgb("#A32020")

#let fills = (
  definition: rgb("#EAF0F7"),
  theorem: rgb("#F6EFE7"),
  example: rgb("#EBF2EA"),
  procedure: rgb("#F2ECF6"),
)

// One counter for every environment, reset at each section.
#let env-kind = "env"
#let env-counter = counter(figure.where(kind: env-kind))

// Section-qualified number of the element at `loc`.
#let number-at(c, loc) = {
  let s = counter(heading).at(loc).first()
  let n = c.at(loc).first()
  [#s.#n]
}

#let env(name, fill: none, title: none, cited: false, body) = figure(
  kind: env-kind,
  supplement: name,
  numbering: (..n) => context {
    let s = counter(heading).get().first()
    numbering("1.1", s, ..n)
  },
  outlined: false,
  block(
    width: 100%,
    fill: fill,
    inset: if fill == none { (x: 0pt, y: 3pt) } else { (x: 9pt, y: 7pt) },
    breakable: true,
    {
      context [*#name #number-at(env-counter, here())*]
      if title != none [ *(#title)*]
      if cited [ (cited)]
      [*.*]
      h(0.5em)
      body
    },
  ),
)

#let definition = env.with("Definition", fill: fills.definition)
#let theorem = env.with("Theorem", fill: fills.theorem)
#let proposition = env.with("Proposition", fill: fills.theorem)
#let lemma = env.with("Lemma", fill: fills.theorem)
#let corollary = env.with("Corollary", fill: fills.theorem)
#let example = env.with("Example", fill: fills.example)
#let procedure = env.with("Procedure", fill: fills.procedure)
#let remark = env.with("Remark")

#let proof(title: none, body) = block(width: 100%, breakable: true)[
  #emph[#if title == none [Proof.] else [#title.]] #body#h(0.6em)#h(1fr)$square.filled$
]

#let solution(body) = block(width: 100%, breakable: true)[
  #emph[Solution.] #body#h(0.6em)#h(1fr)$lozenge.stroked$
]

// Marks unreadable or absent source material; never replaced by a reconstruction.
#let missing(page, body) = text(fill: missing-colour)[\[#page: #body\]]

#let notes(title: none, body) = {
  set document(title: title)
  set page(
    paper: "a4",
    margin: 2.4cm,
    numbering: "1",
    number-align: center,
    header: none,
  )
  set text(font: "TeX Gyre Pagella", size: 11pt, lang: "en")
  show math.equation: set text(font: "New Computer Modern Math")
  set par(justify: true)
  set enum(numbering: "1)", spacing: 1em)
  set par(leading: 0.72em, spacing: 1.4em)
  set block(spacing: 1.4em)

  set heading(numbering: "1.")
  show heading: set block(above: 2.2em, below: 1.1em)
  show heading.where(level: 1): it => {
    env-counter.update(0)
    counter(math.equation).update(0)
    counter(figure.where(kind: image)).update(0)
    set text(size: 14pt, weight: "bold", fill: accent)
    set par(justify: false)
    it
  }
  show heading.where(level: 2): set text(size: 12pt, weight: "bold", fill: accent-dark)

  show figure.where(kind: env-kind): set block(breakable: true, above: 16pt, below: 16pt)
  show figure.where(kind: env-kind): set align(left)
  show figure.where(kind: env-kind): it => it.body

  // Equations are numbered per section, and only when labelled.
  set math.equation(numbering: (..n) => context {
    let s = counter(heading).get().first()
    numbering("(1.1)", s, ..n)
  })
  show math.equation.where(block: true): it => {
    if it.has("label") { it } else [
      #counter(math.equation).update(v => v - 1)
      #math.equation(it.body, block: true, numbering: none) <unnumbered>
    ]
  }

  set table(stroke: 0.5pt + rule-colour, inset: (x: 4pt, y: 4pt), align: center)
  show link: set text(fill: accent)
  // References resolve the section number at the target, not at the reference.
  show ref: it => {
    let el = it.element
    if el == none { return it }
    let loc = el.location()
    let target = if el.func() == figure and el.kind == env-kind {
      [#el.supplement #number-at(env-counter, loc)]
    } else if el.func() == figure and el.kind == image {
      [Figure #number-at(counter(figure.where(kind: image)), loc)]
    } else if el.func() == math.equation {
      [(#number-at(counter(math.equation), loc))]
    } else { return it }
    text(fill: accent, link(loc, target))
  }
  set outline(indent: auto)

  // Figures: non-floating, numbered per section, small italic caption with a bold label.
  set figure(supplement: [Figure], gap: 0.8em)
  set figure(numbering: (..n) => context {
    let s = counter(heading).get().first()
    numbering("1.1", s, ..n)
  })
  show figure.caption.where(kind: image): it => text(size: 9.5pt, style: "italic")[
    *#it.supplement #context it.counter.display(it.numbering).* #it.body
  ]

  align(center, text(size: 17pt, weight: "bold", fill: accent, title))
  v(1em)
  outline(title: [Contents])
  pagebreak()
  body
}
