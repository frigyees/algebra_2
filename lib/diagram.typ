// Commutative diagrams drawn with native primitives (no packages).
// cd(nodes, arrows): nodes are (row, col, content); arrows are dictionaries
//   (from: (r, c), to: (r, c), label: content, side: "left" | "right",
//    dashed: bool, pad: (start, end) in pt, both: bool for <->).

#let _pt(l) = l / 1pt

#let _head(tip, ang, stroke) = {
  let s = 4.2
  let wing(a) = place(line(
    start: (tip.at(0) * 1pt, tip.at(1) * 1pt),
    end: ((tip.at(0) + s * calc.cos(a)) * 1pt, (tip.at(1) + s * calc.sin(a)) * 1pt),
    stroke: stroke,
  ))
  wing(ang + 150deg)
  wing(ang - 150deg)
}

#let cd(nodes, arrows, dx: 2.1cm, dy: 1.45cm, pad: (15, 13)) = {
  let rows = calc.max(..nodes.map(n => n.at(0))) + 1
  let cols = calc.max(..nodes.map(n => n.at(1))) + 1
  let margin = (28, 12)
  let pos(rc) = (margin.at(0) + rc.at(1) * _pt(dx), margin.at(1) + rc.at(0) * _pt(dy))
  let w = 2 * margin.at(0) + (cols - 1) * _pt(dx)
  let h = 2 * margin.at(1) + (rows - 1) * _pt(dy)
  align(center, box(width: w * 1pt, height: h * 1pt, {
    for (r, c, body) in nodes {
      let (x, y) = pos((r, c))
      place(dx: x * 1pt, dy: y * 1pt,
        box(width: 0pt, height: 0pt, align(center + horizon, box(width: 4cm, align(center, $#body$)))))
    }
    for a in arrows {
      let (x1, y1) = pos(a.from)
      let (x2, y2) = pos(a.to)
      let (vx, vy) = (x2 - x1, y2 - y1)
      let len = calc.sqrt(vx * vx + vy * vy)
      let (ux, uy) = (vx / len, vy / len)
      let p = a.at("pad", default: none)
      let sh(i) = if p != none { p.at(i) } else { pad.at(0) * calc.abs(ux) + pad.at(1) * calc.abs(uy) }
      let s = (x1 + ux * sh(0), y1 + uy * sh(0))
      let e = (x2 - ux * sh(1), y2 - uy * sh(1))
      let dashed = a.at("dashed", default: false)
      let stroke = if dashed { (paint: black, thickness: 0.55pt, dash: "dashed") } else { 0.55pt }
      place(line(start: (s.at(0) * 1pt, s.at(1) * 1pt), end: (e.at(0) * 1pt, e.at(1) * 1pt), stroke: stroke))
      let ang = calc.atan2(ux, uy)
      _head(e, ang, 0.55pt)
      if a.at("both", default: false) { _head(s, ang + 180deg, 0.55pt) }
      let label = a.at("label", default: none)
      if label != none {
        let side = if a.at("side", default: "left") == "left" { 1 } else { -1 }
        let off = 7.5
        let (nx, ny) = (uy * side, -ux * side)
        let mx = (s.at(0) + e.at(0)) / 2 + nx * off
        let my = (s.at(1) + e.at(1)) / 2 + ny * off
        place(dx: mx * 1pt, dy: my * 1pt,
          box(width: 0pt, height: 0pt, align(center + horizon, box(width: 3cm, align(center, text(size: 8.5pt, $#label$))))))
      }
    }
  }))
}

// Inline exact sequences: seq(M_1, f_1, M_2, f_2, M_3, ...)
#let ar(l) = $stretch(arrow.r, size: #2.4em)^#l$
