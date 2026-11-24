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

// Editions. Every environment, proof and solution states its provenance with
// `status:`; these tags are the authoritative record of what is lecture content.
// `typst compile --input edition=course` keeps only blocks whose status is in
// `course-statuses`. Omitted environments keep their numbers, so both editions
// and ledger.md share one numbering.
#let edition = sys.inputs.at("edition", default: "full")
#assert(edition in ("full", "course"), message: "edition must be full or course")
#let statuses = ("S", "S+", "C", "I", "A", "B")
#let course-statuses = ("S", "S+", "C")
#let shown(status) = {
  assert(status in statuses, message: "ledger status must be one of " + statuses.join(", "))
  edition == "full" or status in course-statuses
}
// An omitted environment keeps an invisible placeholder body, so that it is still
// counted and references to it resolve.
#let placeholder = metadata("omitted")

#let env(name, fill: none, title: none, cited: false, status: none, body) = figure(
  kind: env-kind,
  supplement: name,
  numbering: (..n) => context {
    let s = counter(heading).get().first()
    numbering("1.1", s, ..n)
  },
  outlined: false,
  if not shown(status) { placeholder } else { block(
    width: 100%,
    fill: fill,
    inset: if fill == none { (x: 0pt, y: 3pt) } else { (x: 9pt, y: 7pt) },
    breakable: true,
    {
      context [*#name #number-at(env-counter, here())*]
      if title != none [ (#title)]
      if cited [ (cited)]
      [*.*]
      [ ]
      body
    },
  ) },
)

// True for an environment omitted from the current edition.
#let omitted(fig) = fig.body.func() == metadata

#let definition = env.with("Definition", fill: fills.definition)
#let theorem = env.with("Theorem", fill: fills.theorem)
#let proposition = env.with("Proposition", fill: fills.theorem)
#let lemma = env.with("Lemma", fill: fills.theorem)
#let corollary = env.with("Corollary", fill: fills.theorem)
#let example = env.with("Example", fill: fills.example)
#let procedure = env.with("Procedure", fill: fills.procedure)
#let remark = env.with("Remark")

#let proof(title: none, status: none, body) = if shown(status) [#block(width: 100%, breakable: true)[
  #emph[#if title == none [Proof.] else [#title.]] #body#h(0.6em)#h(1fr)$square.filled$
]] else { none }

#let solution(status: none, body) = if shown(status) [#block(width: 100%, breakable: true)[
  #emph[Solution.] #body#h(0.6em)#h(1fr)$lozenge.stroked$
]] else { none }

// Material inside or between blocks that is not lecture content (ledger status A or B).
#let extra(status: "A", body) = if shown(status) { body } else { none }

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
  set text(font: "TeX Gyre Pagella", size: 10.5pt, lang: "en")
  show math.equation: set text(font: "New Computer Modern Math")
  set par(justify: true)
  set enum(numbering: "1)", spacing: 1em)
  // LaTeX paragraphs: no gap between paragraphs, first-line indent, no indent
  // after a heading, display, list, proof or environment box (all: false).
  set par(leading: 0.72em, spacing: 0.72em, first-line-indent: (amount: 1.5em, all: false))
  set block(spacing: 1.4em)
  // Display math: close to \abovedisplayskip / \belowdisplayskip.
  show math.equation.where(block: true): set block(above: 0.85em, below: 0.85em)

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
  show figure.where(kind: env-kind): it => if omitted(it) { none } else { it.body }

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
    if el.func() == figure and el.kind == env-kind and omitted(el) {
      return [#el.supplement #number-at(env-counter, loc) (full edition)]
    }
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
  if edition == "course" {
    v(0.4em)
    align(center, text(size: 10pt, style: "italic")[Lecture content only. Numbering follows the full edition; omitted blocks leave gaps.])
  }
  v(1em)
  outline(title: [Contents])
  pagebreak()
  body
}
