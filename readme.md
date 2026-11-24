# Algebra 2

Lecture material digitalized from handwritten notes taken at Algebra 2 lectures.

## Build

```sh
just full    # full edition: algebra_2.pdf
just course  # lecture content only: algebra_2_course.pdf
just c       # both
just wf      # watch the full edition (just wc: course edition)
just wc      # watch the lecture content-only edition
```

## Editions

Every environment, proof and solution carries its status, defined in `ledger.md` e.g. `#theorem(status: "S+")[...]`. Added material inside or between blocks is wrapped in `#extra[...]` (status A by default). The course edition (`--input edition=course`) keeps statuses S, S+ and C and drops I, A and B. Omitted environments keep their numbers, so the two editions and `ledger.md` share one numbering; a reference to an omitted block prints "(full edition)". Granularity is per block: an S+ block keeps its supplied steps in the course edition unless they are wrapped in `#extra`.

The `status:` tags in the source are authoritative. `ledger.md` records why a block diverges from the scans.

## Repo layout

- `lib/style.typ`: page, environments, counter, references
- `lib/macros.typ`: notation
- `lib/diagram.typ`: commutative diagrams
- `src/NN-YYMMDD.typ`: one fragment per lecture, sections follow topics and may span fragments
- `ledger.md`: reasons for every divergence from the scans (corrections, completions, additions)
