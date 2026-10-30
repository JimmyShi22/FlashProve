-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Index.lean: the honest prover's side of an attention segment's own rounds:
the parts on the row maximum and its index. Definitions with code; no theorem. The tests are in
Johnson/Desc/K5/Honest/IndexToy.lean.

What these rounds are for. The prover has committed, for each pair b, head hk of keys and values and
token i, to a row maximum and to the bits of an index. It states the maxima at a drawn point and
runs three masked sumchecks: the maximum is the query times the key at the index; the key at the
index is the key that the index's cells select; the index's cells are bits. The verifier's side is
Johnson/Desc/First/Att/K5AttentionKind.lean (the rounds), LeftP.lean (the summands at the challenges) and
RunsP.lean, `claim7` and `claim8` (what each end value is a value of). The names M6, SF, SD, HB, KC
and IBP are those of docs/format/11-3-attention-segment.md.

  `maxOf`         the verifier's named points on the maximum and its index, at the challenges so far
  `atF`, `atD`, `atH`   the same points with a point laid in the place of one sumcheck's challenges:
                  the verifier's own accessors then cut that point
  `keyAtIndex`    the sum over j of kx(j) times the product over k of eq1(ibit_k, bit k of j)
  `pairsOf`       the terms of a sum of weighted products of two maps
  `m6`            M6_b: the row maxima of pair b at the point (tg, ti)
  `sSF`           the summand "the score at the index", on the cube (i, hk, ch)
  `sSD`           the summand "the key at the index", on the cube (j, hk, i)
  `sHB`           the summand "the index's cells are bits", on the cube (i, hk, k), k of 4 bits

What is taken from the verifier's text and not typed again: every cut of a point (`MaxP.ri` ..
`MaxP.rk`, `tg`, `ti`: Att/Points.lean) and the weights of SF and HB (`wAtIndex`, `wCells`:
Att/K5LeftAll.lean, which are the lines of `leftP`, by that file's `leftP_spec`). The terms of SD
follow `leftKey` (Att/LeftP.lean).

Two choices. The second map of SF is typed with no decoded index: on the cube it is `keyAtIndex`,
and off the cube it is the extension of that table of degree at most 1 in each variable, not the
formula with the cells' maps in it, which would have a higher degree in i. So typed, SD's sum is
meant to be the batched second end values of SF at every reader of cells, bits or not: the tests
hold that at two made-up places; it is not proved. The second map of HB is the first minus 1. It is
an end value of its own number, with the 1 inside the map: the verifier multiplies what is shown
under the two numbers.

Limits. The place's numbers are read of the shape. That the numbers of these rounds, the other field
of the public data, are the same is tested only at made-up places, where both are laid by hand.
Heads, tokens and channels run to the powers of two of their numbers of bits, where the verifier's
sums over the heads run to the shape's number of heads. Where the verifier's `pointsOf` refuses, the
named points are empty and what is computed has no meaning. A challenge that has not been heard
reads as 0. That the maps are what the commitments hold is not the matter of this file.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Terms
import Johnson.Desc.K5.Honest.Points
import Johnson.Desc.First.Att.K5LeftAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Aff)
open VerifiableInference.Desc.First.Att.P (Geo MaxP SumP eqTab eqPts wAtIndex wCells)

/-! ## The verifier's points -/

/-- **The verifier's named points on the maximum and its index**, at the challenges so far; all
empty where its function refuses. -/
def maxOf (P : Pub5) (c : Chal) : MaxP :=
  let z : SumP := ⟨#[], 0, Aff.ofConst zeroE⟩
  ((ptsOf P c).map (·.x)).getD ⟨#[], #[], 0, z, z, z⟩

/-- The named points with the point x in the place of the challenges of SF; of SD; of HB. No other
field is made of these challenges (Att/Points.lean: the last lines of `pointsOf`). -/
def atF (m : MaxP) (x : List E) : MaxP := { m with scF := { m.scF with r := x.toArray } }
def atD (m : MaxP) (x : List E) : MaxP := { m with scd := { m.scd with r := x.toArray } }
def atH (m : MaxP) (x : List E) : MaxP := { m with scH := { m.scH with r := x.toArray } }

/-! ## Small parts -/

/-- **The key that the index's cells select**, at pair b, head hk, token i and channel ch: the sum
over the tokens j of kx(j) times the product over k below lt of eq1(ibit_k, bit k of j), where
eq1(s, y) = s y + (1 - s)(1 - y). If the cells are the bits of a number, it is the key at that
token. -/
def keyAtIndex (lt HA : Nat) (w : K5In) (b hk i ch : Nat) : E :=
  sumTo (2 ^ lt) fun j =>
    (List.range lt).foldl (fun p k =>
      let s := w.ibit k b hk i
      mulE p (if (j >>> k) % 2 == 1 then s else subE oneE s)) (w.kx (b / HA) hk j ch)

/-- The terms W_b e_(2b) e_(2b+1), b below n. -/
def pairsOf (n : Nat) (W : Array E) : List Term :=
  (List.range n).map fun b => ⟨W.getD b zeroE, [⟨oneE, 2 * b, zeroE⟩, ⟨oneE, 2 * b + 1, zeroE⟩]⟩

/-! ## The maxima -/

/-- **M6_b**, b below NP: the sum over hk and i of eq(tg, hk) eq(ti, i) mx b hk i. -/
def m6 (P : Pub5) (w : K5In) (c : Chal) : List E :=
  let m := maxOf P c
  let (eg, ei) := (eqTab m.tg, eqTab m.ti)
  (List.range P.g.NP).map fun b => under eg fun hk => under ei fun i => w.mx b hk i

/-! ## The score at the index -/

/-- **SF.** The cube is (i, hk, ch). The weight of pair b is om_b eq(tg, hk) eq(ti, i); the first
map is the query; the second is the key that the index's cells select. -/
def sSF (P : Pub5) (w : K5In) (c : Chal) : Summand :=
  let g := P.g
  let m := maxOf P c
  let h := heardAt P c fun _ => none
  let (G, D) := (2 ^ g.lgk, 2 ^ g.ldh)
  -- the maps on the cube, number by number: the entry (i G + hk) D + ch
  let tabs : Array (Array E) := (Array.range (2 * g.NP)).map fun n =>
    (Array.range (2 ^ g.lt * G * D)).map fun e =>
      let (i, hk, ch) := (e / (D * G), e / D % G, e % D)
      if n % 2 == 0 then w.q (n / 2) hk i ch else keyAtIndex g.lt g.HA w (n / 2) hk i ch
  { vars := g.lt + g.lgk + g.ldh
    ends := 2 * g.NP
    endAt := fun x n =>
      let y := atF m x
      let (ei, eg, ec) := (eqTab (y.ri g), eqTab (y.rg g), eqTab (y.rc g))
      let t := tabs.getD n #[]
      under ei fun i => under eg fun hk => under ec fun ch => t.getD ((i * G + hk) * D + ch) zeroE
    terms := fun x => pairsOf g.NP (wAtIndex g { h with atIndex := sumAt x.toArray }) }

/-! ## The key at the index -/

/-- **SD.** The cube is (j, hk, i). The end values are KC_lam, lam below Lam, and then IBP_(b,k)
under the number Lam + b lt + k. KC_lam is the key of layer lam at (j, hk), with the channel at SF's
challenges; IBP_(b,k) is cell k of the index of pair b at (hk, i). The term of pair b is eq(riF, i)
eq(rgF, hk) om'_b KC_(b / HA) times the product over k of (IBP_(b,k) (2 y_k - 1) + 1 - y_k), y_k the
coordinate of bit k of j. -/
def sSD (P : Pub5) (w : K5In) (c : Chal) : Summand :=
  let g := P.g
  let m := maxOf P c
  let om' := (heardAt P c fun _ => none).om'
  let (lt, Lam, G) := (g.lt, g.Lam, 2 ^ g.lgk)
  let (riF, rgF, ec) := (m.ri g, m.rg g, eqTab (m.rc g))
  -- KC on the cube, layer by layer: the entry j G + hk
  let kc : Array (Array E) := (Array.range Lam).map fun lam =>
    (Array.range (2 ^ lt * G)).map fun n => under ec fun ch => w.kx lam (n % G) (n / G) ch
  { vars := 2 * lt + g.lgk
    ends := Lam + g.NP * lt
    endAt := fun x n =>
      let y := atD m x
      let eg := eqTab (y.pg g)
      if n < Lam then
        let (ej, t) := (eqTab (y.pj g), kc.getD n #[])
        under ej fun j => under eg fun hk => t.getD (j * G + hk) zeroE
      else
        let ei := eqTab (y.pi g)
        under eg fun hk => under ei fun i => w.ibit ((n - Lam) % lt) ((n - Lam) / lt) hk i
    terms := fun x =>
      let y := atD m x
      let pj := y.pj g
      let f := mulE (eqPts riF (y.pi g)) (eqPts rgF (y.pg g))
      (List.range g.NP).map fun b =>
        ⟨mulE f (om'.getD b zeroE), ⟨oneE, b / g.HA, zeroE⟩ :: (List.range lt).map fun k =>
          let yk := pj.getD (lt - 1 - k) zeroE
          ⟨subE (addE yk yk) oneE, Lam + b * lt + k, subE oneE yk⟩⟩ }

/-! ## The index's cells are bits -/

/-- **HB.** The cube is (i, hk, k), k of 4 bits. The weight of pair b is om''_b eq(tbi, i) eq(tbg,
hk) eq(tk, k); the first map is cell k of the index for k below lt and 0 for the other k; the second
is the first minus 1. -/
def sHB (P : Pub5) (w : K5In) (c : Chal) : Summand :=
  let g := P.g
  let m := maxOf P c
  let h := heardAt P c fun _ => none
  let first (x : List E) (b : Nat) : E :=
    let y := atH m x
    let (ei, eg, ek) := (eqTab (y.ri2 g), eqTab (y.rg2 g), eqTab (y.rk g))
    sumTo g.lt fun k => mulE (ek.getD k zeroE)
      (under eg fun hk => under ei fun i => w.ibit k b hk i)
  { vars := g.lt + g.lgk + 4
    ends := 2 * g.NP
    endAt := fun x n => if n % 2 == 0 then first x (n / 2) else subE (first x (n / 2)) oneE
    terms := fun x => pairsOf g.NP (wCells g { h with cells := sumAt x.toArray }) }

end H2K5.Honest
