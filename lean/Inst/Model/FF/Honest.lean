-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/FF/Honest.lean: the honest trace (`hon`, Inst/Model/FF/Trace.lean) of a feed-forward
  segment satisfies the relation over the integers, under `Par` (Inst/Model/FF/HonestKeys.lean),
  `Unit.TabOK` (Inst/Model/Common/Unit.lean), `Runs` (Inst/Model/FF/Trace.lean); in the first
  segment, if x 0 is the embedding of the prompt.

    `honest_gen`   the four clauses of its statement for arbitrary sizes with `Par`, tables with
                   `Unit.TabOK`, arbitrary integer weights and every run of the steps of the segment
                   (`Runs`)
    `honest`       `Spec.honest` of Inst/Model/FF/Trace.lean, for valid scales
  No bound on the weights is used: the states of the stream and the outputs of attention are bounded
  by `Runs` (`wr`, `o`), sel, lr and xr by `Router.hon_ranges` (Inst/Model/Common/Router.lean);
  every other honest value is a quotient whose range condition the integer program
  (Inst/Model/Program.lean) checks, the output of a clamp or of a table, a remainder, or a digit.

  Scales: the instance argument `[scl : Scl]` (Inst/Model/Scl.lean, Inst/Model/FF/Index.lean). "the
  reference parameters": the sizes `Dim.ref`, with any scales (valid ones under `[Lawful]`,
  Inst/Model/FF/Lawful.lean). A theorem marked "omit scl in" reads no scale.
-/
import Inst.Model.FF.HonestCells

set_option autoImplicit false

/- The default instance `Scl.ref` (the reference scales) is switched off in this file: whatever
reads scales takes `[scl : Scl]`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.FFSeg.Hon

variable [scl : Scl]

open Inst.Model.TableKeys (InLutZ)

omit scl in
theorem mem_lutSet {L : Lut} {v : ℤ} (h : InLutZ L v) : v ∈ lutSet (R := ℤ) L := by
  obtain ⟨ι, h1, h2⟩ := h
  exact ⟨ι, h1, by rw [h2, Int.cast_id]⟩

/-- Under `Par`, `Unit.TabOK` and `Runs`, the honest trace satisfies the relation over the integers,
for arbitrary sizes, and (J11) in the first segment, if the stream at the index 0 is the embedding
of the prompt. -/
theorem honest_gen {D : Dim} {tb : Tables} {w : ℕ → LayerW} {L0 : ℕ} {x o : ℕ → ℕ → Vec}
    (hp : Par D L0) (tab : Unit.TabOK tb) (R : Runs D tb w L0 x o) (emb : ℕ → ℕ → ℤ) (tok : ℕ → ℕ) :
    (∀ c : Cell, c.Valid D → |hon D tb w L0 x o c| ≤ 128) ∧
    (∀ (X : Arr) (n j i : ℕ), val (hon D tb w L0 x o) X n j i = hv D tb w L0 x o X n j i) ∧
    (∀ q : KeyName D,
      key D (hon D tb w L0 x o) tb L0 (fun l => LW.ofInt ℤ (w l))
          q.val.1 q.val.2.1 q.val.2.2.1 q.val.2.2.2 ∈
        lutSet (R := ℤ) (lut tb (call q.val.1))) ∧
    ∀ first : Bool, (first = true → ∀ i < D.T, ∀ j < D.d, x 0 i j = emb (tok i) j) →
      ∀ j : Idn, j.Valid D first → idnVal D (hon D tb w L0 x o) emb tok j = 0 :=
  ⟨abs_hon_le hp tab R,
    val_hon D tb w L0 x o,
    fun q =>
      mem_lutSet
        (key_hon hp R q.val.1 q.property.1 q.property.2.1 q.property.2.2.1 q.property.2.2.2),
    fun first hf => idn_hon hp R emb tok first hf⟩

/-- `Par` holds at the reference parameters, for valid scales and an even L0. -/
theorem par_ref [Lawful] {L0 : ℕ} (hL : L0 % 2 = 0) : Par Dim.ref L0 where
  even := hL
  nx := by decide
  T := by decide
  f := by decide
  d := by decide
  kq := fun l => (Lawful.all l).rq.2
  kk := fun l => (Lawful.all l).rk.2
  kv := fun l => (Lawful.all l).rv.2
  ko := fun l => (Lawful.all l).ro.2
  kd := fun l => (Lawful.all l).rd.2
  kr := fun l => (Lawful.all l).rr.2
  kg := fun l => (Lawful.all l).rg.2
  ku := fun l => (Lawful.all l).ru.2
  kg' := fun l => (Lawful.all l).rg'.2
  ku' := fun l => (Lawful.all l).ru'.2
  n1 := fun l => (Lawful.all l).n1
  n2 := fun l => (Lawful.all l).n2

/-- The proof of `Spec.honest` (Inst/Model/FF/Trace.lean), for valid scales. It says, at the
reference sizes, under `Setting` and `Runs`: (a) every valid cell of the honest trace is at most 128
in absolute value (128 included: the widened cell rule of Inst/Model/Widened.lean), and the read-out
of every array is its honest value at the array's own indices; (b) every key of the relation
(`KeyName`) is an entry of its table, as an integer; (c) the identities (J1) to (J10) hold over the
integers, and in the first segment (J11), if x 0 is the embedding of the prompt. -/
theorem honest [Lawful] : Spec.honest := by
  intro tb W L0 tok hS x o R
  obtain ⟨h1, h2, h3, h4⟩ := honest_gen
    (par_ref hS.even) (Unit.TabOK.of_ok hS.tab) R (Layout.weightsOf ppref Layout.kRef W).Emb tok
  exact ⟨h1, fun X n j i _ _ _ => h2 X n j i, h3, h4⟩

end Inst.Model.FFSeg.Hon
