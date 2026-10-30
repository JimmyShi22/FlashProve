-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CorePeelRec.lean: the written link's five rounds are taken off over the format with a
sample map, at any pair of records.

OnBytes/Slice/CorePeel.lean reduces the soundness of the written link to a statement on the rounds
after the fifth, by the library's theorems on its link protocol (Cb/Ld/LdLink.lean). There the
format is the base format `Sz.ix` (OnBytes/Slice/LinkAt.lean), whose sample map is `Sample.nil`,
and the instance of the library's first joint is the pair of empty records. The library's
link is stated for any sample map of a row and any pair of records. This file says
OnBytes/Slice/CorePeel.lean's last part again over the format with a sample map Z (`Sz.ixR`,
OnBytes/Slice/LinkAtIxR.lean), at any pair of records r. The text of `st2R`, `peel_sendR`, `st4R`,
`coreErrR` and `core_peelR` is that of `st2`, `peel_send`, `st4`, `coreErr` and `core_peel`, cut by
a program: the link over `ixR Z` for the link, r for the pair of empty records. The written rounds
and `DrawsOK` are those of that file; the family of the two folded rows' oracle messages and its
seeds are those of OnBytes/Slice/LinkAt.lean. The error counts are that file's (`coreErrR_eq`).

Main definitions: `Sz.lwR`, `Sz.lkR`, `st2R`, `st4R`, `coreErrR`.
Main theorems: `peel_sendR`, `coreErrR_eq`, `core_peelR`.

Not claimed. All that OnBytes/Slice/CorePeel.lean does not claim. That the hypothesis on the rounds
after the fifth holds: the statement `st4R` holds the two records, and the last
joint's relation asks the record's row of each fold besides (the library's `LdLkP.Rows`). That an
entry file's chain with a record begins with these five rounds: by the format's own Lean text
(Fmt/M3Plan.lean, "What is not claimed") its plan has a further first entry, and answers stand in
the statement. Nothing on where a record's seed comes from, on how often a record fails to single
one table out, on any radius, on the sizes of the error counts, on a program or a file.

-/
import OnBytes.Slice.CorePeel
import OnBytes.Slice.LinkAtIxR

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

namespace Sz
variable (S : Sz)

/-- The link on vectors, over the format with the sample map Z. -/
@[reducible] noncomputable def lwR (Z : Sample GE S.En) : LdLkW GE S.Pos S.Co S.En S.Lay where
  X := S.ixR Z
  lay := fun a => ⟨a.val, lt_of_lt_of_le a.isLt (Nat.sub_le _ _)⟩
  l := S.P.aPhi
  pl := fun a t => a.val.testBit t.val

/-- **The library's link at these sizes**: `Sz.lk` over the format
with the sample map Z. -/
@[reducible] noncomputable def lkR (Z : Sample GE S.En) : LdLkP GE S.Pos S.Co S.En S.Lay where
  D := S.lwR Z
  Sy := Run.PQ.SgX
  up := fun s r => algebraMap GF GE (toF (s.2.getD (rowNo r) 0))
  e₀ := S.e0
  e₁ := S.e1
  t₀ := S.P.nu0
  t₁ := S.P.nuj
  N := S.fam
  i₀ := false
  l₀ := S.putAt
  i₁ := true
  l₁ := S.putAt

end Sz

/-- The statement after the sending. -/
noncomputable def st2R (S : Sz) (Z : Sample GE S.En) (d2 d3 : PQ.RD) (a : (S.lkR Z).X1 ×
    (S.lkR Z).E0.Str) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) : (S.lkR Z).X2 × (S.lkR Z).E2.Str :=
  ((a.1, fun b => (gSeed (S.P.aR + S.P.aP) _ (valsOf d2 c2), answOf S d3 m3 b)),
    (a.2, wordsOf S d2 m2.1))

/-- **The two rounds of the sending are taken off.** -/
theorem peel_sendR (S : Sz) (Z : Sample GE S.En) (on0 on1 : ((S.lkR Z).D.X.Row → S.Pos → GE) →
    (S.lkR Z).D.X.Rec → Prop)
    (L : Bool → ℕ) (hlist : ∀ a, ((S.lkR Z).N.om a).ListLE (L a)) (hev : ∀ a,
      ((S.lkR Z).N.om a).Evades)
    (d2 d3 : PQ.RD)
    (hg2 : Function.Injective (gSeed (S.P.aR + S.P.aP) (Fmt.dsOf d2.entry d2.kind)))
    (hg3 : Function.Injective (fun _ : Vals .two (Fmt.dsOf d3.entry d3.kind) => ()))
    (hlog2 : d2.entry.logN ≤ 64) (hlog3 : d3.entry.logN ≤ 64) (t : Shape) (εt : Err t)
    (a : (S.lkR Z).X1 × (S.lkR Z).E0.Str) (hno : ∀ w, ¬ ((S.lkR Z).j1 on0 on1).cf.relR a w)
    (bad : Tr (wRound d2 :: wRound d3 :: t) → Prop)
    (hp2 : ∀ m c τ, GChal.pass (b := d2.entry.work) c = false → bad (m, c, τ))
    (hp3 : ∀ m2 c2 m c τ, GChal.pass (b := d3.entry.work) c = false → bad (m2, c2, m, c, τ))
    (H : ∀ m2 c2 m3 c3, (∀ w, ¬ ((S.lkR Z).j2 on0 on1).cf.relR (st2R S Z d2 d3 a m2 c2 m3) w) →
      Doomed t εt fun b => bad (m2, c2, m3, c3, b)) :
    Doomed (wRound d2 :: wRound d3 :: t)
      (ldSendFamErr (S.lkR Z).N S.seeds L * (bsRound .two d2.entry d2.kind).w,
        (0 * (bsRound .two d3.entry d3.kind).w, εt)) bad := by
  refine peel (s := [wRound d2, wRound d3]) (t := t) (ldSendFam (S.lkR Z).N S.seeds (S.lkR Z).X1
    (S.lkR Z).E0).red
    (know_snd (S.lkR Z) on0 on1 S.seeds L (seeds_fair S) hlist hev) a trivial hno
    (two (r₁' := S.fam.sendRound S.seeds) (r₂' := Blocks.plainRound S.fam.Answ Unit fun _ _ => 0)
      (fun m => (wordsOf S d2 m.1, ())) (chalTo d2 (gSeed (S.P.aR + S.P.aP) _))
      (fun m => ((), answOf S d3 m)) (chalTo d3 fun _ => ()))
    (((bsRound .two d2.entry d2.kind).w, ((bsRound .two d3.entry d3.kind).w, ())) : ℕ × ℕ × Unit)
    (two_fib _ _ _ _ _ _ (chalTo_fib d2 _ hg2 hlog2) (chalTo_fib d3 _ hg3 hlog3)) εt bad ?_ ?_
  · rintro ⟨m2, c2, m3, c3, ⟨⟩⟩ hτ0
    have hτ := (two_tr (r₁' := S.fam.sendRound S.seeds)
      (r₂' := Blocks.plainRound S.fam.Answ Unit fun _ _ => 0)
      (fun m => (wordsOf S d2 m.1, ())) (chalTo d2 (gSeed (S.P.aR + S.P.aP) _))
      (fun m => ((), answOf S d3 m)) (chalTo d3 fun _ => ()) m2 c2 m3 c3).symm.trans hτ0
    cases h2 : chalTo d2 (gSeed (S.P.aR + S.P.aP) _) c2 with
    | none => exact doomed_of_all _ _ _ fun b => hp2 m2 c2 _ (chalTo_none d2 _ c2 h2)
    | some s =>
      cases h3 : chalTo d3 (fun _ => ()) c3 with
      | none => exact doomed_of_all _ _ _ fun b => hp3 m2 c2 m3 c3 b (chalTo_none d3 _ c3 h3)
      | some u =>
        rw [h2, h3] at hτ
        cases hτ
  · rintro ⟨m2, c2, m3, c3, ⟨⟩⟩ τ' hτ0 hno'
    have hτ := (two_tr (r₁' := S.fam.sendRound S.seeds)
      (r₂' := Blocks.plainRound S.fam.Answ Unit fun _ _ => 0)
      (fun m => (wordsOf S d2 m.1, ())) (chalTo d2 (gSeed (S.P.aR + S.P.aP) _))
      (fun m => ((), answOf S d3 m)) (chalTo d3 fun _ => ()) m2 c2 m3 c3).symm.trans hτ0
    cases h2 : chalTo d2 (gSeed (S.P.aR + S.P.aP) _) c2 with
    | none =>
      rw [h2] at hτ
      cases hτ
    | some s =>
      cases h3 : chalTo d3 (fun _ => ()) c3 with
      | none =>
        rw [h2, h3] at hτ
        cases hτ
      | some u =>
        rw [h2, h3] at hτ
        obtain rfl := Option.some.inj hτ
        obtain rfl := chalTo_some d2 _ c2 s h2
        exact H m2 c2 m3 c3 fun w => hno' _ w rfl

/-! ## The five rounds -/

section Core
variable (S : Sz) (Z : Sample GE S.En) (r : (S.lkR Z).X0) (d1 d2 d3 d4 d5 : PQ.RD)

/-- **The statement that the library's verifier holds after the five rounds**, as a function of the
two stored strings and of the written messages. -/
noncomputable def st4R (y : (S.lkR Z).E0.Str) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c4 : (wRound d4).Chal)
    (c5 : (wRound d5).Chal) : (S.lkR Z).X4 × (S.lkR Z).E3.Str :=
  let a1 : (S.lkR Z).X1 × (S.lkR Z).E0.Str :=
    ((S.lkR Z).vGam.nx r y (gVec S.P.v _ (valsOf d1 c1)), (S.lkR Z).vGam.g.map y)
  let a2 := st2R S Z d2 d3 a1 m2 c2 m3
  let a3 : (S.lkR Z).X3 × (S.lkR Z).E3.Str :=
    ((S.lkR Z).vLoc.nx a2.1 a2.2 (gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)),
      (S.lkR Z).vLoc.g.map a2.2)
  ((S.lkR Z).vPhi.nx a3.1 a3.2 (gVec S.P.aPhi _ (valsOf d5 c5)), (S.lkR Z).vPhi.g.map a3.2)

/-- The error counts of the five written rounds: the library's, each times w, the sampler's bound on
how many strings of the round's hash blocks give one tuple of drawn values. -/
noncomputable def coreErrR (ε₀ ε₁ : ℕ) (L : Bool → ℕ) {t : Shape} (εt : Err t) :
    Err (wRound d1 :: wRound d2 :: wRound d3 :: wRound d4 :: wRound d5 :: t) :=
  ((S.lkR Z).errGam ε₀ ε₁ * (bsRound .two d1.entry d1.kind).w,
    (ldSendFamErr (S.lkR Z).N S.seeds L * (bsRound .two d2.entry d2.kind).w,
      (0 * (bsRound .two d3.entry d3.kind).w,
        ((S.lkR Z).errLoc * (bsRound .two d4.entry d4.kind).w,
          ((S.lkR Z).errPhi * (bsRound .two d5.entry d5.kind).w, εt)))))

/-- The error counts do not read the sample map: they are those of OnBytes/Slice/CorePeel.lean. -/
theorem coreErrR_eq (ε₀ ε₁ : ℕ) (L : Bool → ℕ) {t : Shape} (εt : Err t) :
    coreErrR S Z d1 d2 d3 d4 d5 ε₀ ε₁ L εt = coreErr S d1 d2 d3 d4 d5 ε₀ ε₁ L εt := rfl

/-- **The link's five rounds are taken off.** OnBytes/Slice/CorePeel.lean's head tells the
statement; where that head's instance is the pair of empty records, here it is any pair of records
r. -/
theorem core_peelR (on0 on1 : ((S.lkR Z).D.X.Row → S.Pos → GE) → (S.lkR Z).D.X.Rec → Prop)
    (ε₀ ε₁ : ℕ)
    (L : Bool → ℕ) (hFold : (S.lkR Z).FoldErr on0 on1 ε₀ ε₁) (hpl : Function.Injective
      (S.lkR Z).D.pl)
    (hlist : ∀ a, ((S.lkR Z).N.om a).ListLE (L a)) (hev : ∀ a, ((S.lkR Z).N.om a).Evades)
    (hd : DrawsOK S d1 d2 d3 d4 d5) (t : Shape) (εt : Err t) (y : (S.lkR Z).E0.Str)
    (hy : ∀ w, ¬ ((S.lkR Z).j0 on0 on1).cf.relR (r, y) w)
    (bad : Tr (wRound d1 :: wRound d2 :: wRound d3 :: wRound d4 :: wRound d5 :: t) → Prop)
    (hp1 : ∀ m1 c1 τ, GChal.pass (b := d1.entry.work) c1 = false → bad (m1, c1, τ))
    (hp2 : ∀ m1 c1 m2 c2 τ, GChal.pass (b := d2.entry.work) c2 = false → bad (m1, c1, m2, c2, τ))
    (hp3 : ∀ m1 c1 m2 c2 m3 c3 τ, GChal.pass (b := d3.entry.work) c3 = false →
      bad (m1, c1, m2, c2, m3, c3, τ))
    (hp4 : ∀ m1 c1 m2 c2 m3 c3 m4 c4 τ, GChal.pass (b := d4.entry.work) c4 = false →
      bad (m1, c1, m2, c2, m3, c3, m4, c4, τ))
    (hp5 : ∀ m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 τ, GChal.pass (b := d5.entry.work) c5 = false →
      bad (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, τ))
    (H : ∀ m1 c1 m2 c2 m3 c3 m4 c4 m5 c5,
      (∀ w, ¬ (S.lkR Z).j4.cf.relR (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5) w) →
      Doomed t εt fun b => bad (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, b)) :
    Doomed _ (coreErrR S Z d1 d2 d3 d4 d5 ε₀ ε₁ L εt) bad :=
  peel_peek (S.lkR Z).vGam (know_gam (S.lkR Z) on0 on1 ε₀ ε₁ hFold) d1 _ hd.g1 hd.l1 _ _
    (r, y) hy bad hp1 fun m1 c1 h1 =>
  peel_sendR S Z on0 on1 L hlist hev d2 d3 hd.g2 hd.g3 hd.l2 hd.l3 _ _ _ h1 _ (hp2 m1 c1)
    (hp3 m1 c1) fun m2 c2 m3 c3 h2 =>
  peel_peek (S.lkR Z).vLoc (know_loc (S.lkR Z) on0 on1 S.seeds) d4 _ hd.g4 hd.l4 _ _ _ h2 _
    (hp4 m1 c1 m2 c2 m3 c3) fun m4 c4 h3 =>
  peel_peek (S.lkR Z).vPhi (know_phi (S.lkR Z) hpl) d5 _ hd.g5 hd.l5 t εt _ h3 _
    (hp5 m1 c1 m2 c2 m3 c3 m4 c4) fun m5 c5 h4 => H m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 h4

end Core

end OnBytes.Slice
