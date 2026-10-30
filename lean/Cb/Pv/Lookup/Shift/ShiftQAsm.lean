-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Shift/ShiftQAsm.lean.
The shift's round laid before an assembled lookup.

P.lk: the library's record of a lookup's claim (Lk, Cb/Ld/LdLkp.lean) at the shifted vectors. P.lkA
  several b: a block b that proves P.lk, with the shift before it: several = true: the draw of θ,
  then b; several = false: no round: the map st ↦ (st, 0), then b.
Main statements.
  shiftQ_lk: the draw is good from "each key lies among its call's rows" to the in-joint of a block
    that proves P.lk.
  shiftQ_before: for any block b that is good from that joint to a joint C, P.lkA several b is good
    from the in-claim to C.
  shiftQ_asm2_base: b the library's assembled lookup (LkAsm2.baseA) at the shifted vectors, by
    ldLkpAsm2_base as it stands.
  shiftQ_ll: errors and numbers of values: 2^d before b's, or b's alone. shiftQ_run: an honest run
    of the shift's block.
Premises: P.Ok several (several calls: P.Tags; one call: all indices are of one call); that Mu
follows from R0 and the out-claim (as the field muFrom of LdPreD.OK, Cb/Req1/LdSegRefLkpPre.lean);
in shiftQ_asm2_base also P.v = A0.v' + 1 and P.d = A0.d (as numV, numD there, with v, d for g + v,
g + d), Adm p and MuOn Mu.

-/
import Cb.Pv.Lookup.Shift.ShiftQ
import Cb.Ld.LdLkpAsm2Proofs
import Cb.Ld.LdLkpSegTProofs
import Cb.Ld.LdLkpAsmErrProofs

set_option autoImplicit false

namespace Cb.LdLkp
open Finset Cb.Lkp Iop IOR

namespace ShiftQ
variable {E St J M : Type} [Field E]

/-- the calls, read off the tuples -/
def on (P : ShiftQ E St (J → E)) (msg : M → J → E) : ShiftQ E St M :=
  { P with key := fun st ms => P.key st (msg ms) }

/-- the one lookup claim after the shift: the library's record -/
def lk (P : ShiftQ E St (J → E)) : Lk E (St × E) (J → E) :=
  ⟨P.v, P.d, fun x m => shKeyQ P.fK (P.key x.1 m) P.tag x.2,
      fun x => shTabQ P.fT (P.tab x.1) P.tag x.2,
    fun _ _ => True⟩

/-- what rides along, read at an explicit part that holds the shift (LdPreD.R1's words) -/
def ride {Kc Wp : Type} {Ex : ExtSpec} (R0 : Rels Kc St Ex (M × Wp)) : Rels Kc (St × E) Ex (M × Wp)
    :=
  ⟨fun x y w => R0.rel x.1 y w, fun a w => R0.relR (a.1.1, a.2) w, fun a => R0.on (a.1.1, a.2),
      R0.core⟩

/-- R0 with a further clause on the exact side alone -/
def addP {Kc Wp : Type} {Ex : ExtSpec} (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E)
    (Φ : St → (J → E) → Prop) : Rels Kc St Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x y w ∧ Φ x (msg w.1), R0.relR, R0.on, R0.core⟩

variable [Fintype E]

/-- the shift's block (LdPreD.shBk's words, with 2 ^ d) -/
noncomputable def bk (P : ShiftQ E St (J → E)) (Kc M Wp : Type) (Ex : ExtSpec) : BkA Kc M St
    (St × E) Ex Wp :=
  ⟨IOR.draw E Prod.mk Ex, Honest.draw E Prod.mk Ex (M × Wp), Nums.draw Kc E Prod.mk Ex (2 ^ P.d)⟩

/-- the shift, if there are several calls, then the block b -/
noncomputable def lkA (P : ShiftQ E St (J → E)) {Kc M Wp Xo : Type} {Ex : ExtSpec} (several : Bool)
    (b : BkA Kc M (St × E) Xo Ex Wp) : BkA Kc M St Xo Ex Wp :=
  match several with
  | true => (P.bk Kc M Wp Ex).seq b
  | false => b.preM fun st => (st, (0 : E))

/-- What is asked: several calls: the tags; one call: all indices are of one call. -/
def Ok (P : ShiftQ E St (J → E)) (several : Bool) : Prop :=
  match several with
  | true => P.Tags
  | false => ∀ X < 2 ^ P.v, ∀ Y < 2 ^ P.d, P.fT Y = P.fK X

/-- The library's assembled lookup at the shifted vectors (LdPreD.A's words). A0's fields St,
key, tab are not read. -/
def asm (A0 : LkAsm2 E) (P : ShiftQ E St (A0.J → E)) : LkAsm2 E :=
  { A0 with
    St := St × E, key := fun x m => shKeyQ P.fK (P.key x.1 m) P.tag x.2,
    tab := fun x => shTabQ P.fT (P.tab x.1) P.tag x.2 }

end ShiftQ
end Cb.LdLkp

namespace Cb.Spec
open Finset Prob Cb.Lkp Cb.LdLkp Iop IOR

section
variable (E : Type) [Field E] [Fintype E]

/-- The draw, from the calls' claim to the in-joint of a lookup's block. -/
def shiftQ_lk : Prop :=
  ∀ (St J M Wp Kc : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E)) (Mu : St × E → (J → E) → Prop)
      (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E),
    P.Tags →
    (∀ (x : St × E) y w, R0.rel x.1 y w → (P.on msg).outC x w.1 → Mu x (msg w.1)) →
    (P.bk Kc M Wp Ex).Good ((P.on msg).jIn R0) (cj (ShiftQ.ride R0) msg id (P.lk.inP Mu) P.lk.inR)

/-- Before any block that proves the one lookup claim. With one call the premise on Mu is read at
the shift 0 alone. -/
def shiftQ_before : Prop :=
  ∀ (St J M Wp Kc Xo : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E)) (Mu : St × E → (J → E) → Prop)
      (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) (several : Bool)
      (b : BkA Kc M (St × E) Xo Ex Wp) (C : Rels Kc Xo Ex (M × Wp)),
    P.Ok several →
    (∀ (x : St × E) y w, (several = false → x.2 = 0) →
      R0.rel x.1 y w → (P.on msg).outC x w.1 → Mu x (msg w.1)) →
    b.Good (cj (ShiftQ.ride R0) msg id (P.lk.inP Mu) P.lk.inR) C →
    (P.lkA several b).Good ((P.on msg).jIn R0) C

/-- Before the library's assembled lookup, by ldLkpAsm2_base as it stands. -/
def shiftQ_asm2_base : Prop :=
  ∀ (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsm2 E) (P : ShiftQ E St (A0.J → E))
      (Mu : St × E → (A0.J → E) → Prop) (Ex : ExtSpec) (Kc M Wp : Type)
      (R0 : Rels Kc St Ex (M × Wp)) (msg : M → A0.J → E) (several : Bool),
    P.Ok several → P.v = A0.v' + 1 → P.d = A0.d →
    (∀ (x : St × E) y w, (several = false → x.2 = 0) →
      R0.rel x.1 y w → (P.on msg).outC x w.1 → Mu x (msg w.1)) →
    (P.asm A0).H.lkb.Adm p → (P.asm A0).H.MuOn Mu →
    (P.lkA several ((P.asm A0).baseA Ex M Wp Kc msg)).Good ((P.on msg).jIn R0)
      (cj (ShiftQ.ride R0) msg Prod.fst ((P.asm A0).lk.out id id) ((P.asm A0).lk.out id id))

/-- Errors and numbers of values: one round more, with the count 2 ^ d of |E|, if and only if there
are several calls. -/
def shiftQ_ll : Prop :=
  ∀ (St J M Wp Kc Xo : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E))
      (b : BkA Kc M (St × E) Xo Ex Wp)
      (es vs : List ℕ), LL b es vs →
    LL (P.lkA true b) ([2 ^ P.d] ++ es) ([Fintype.card E] ++ vs) ∧ LL (P.lkA false b) es vs

/-- AN HONEST RUN of the shift's block: from a true claim, at every verifier randomness and coin,
the verifier outputs what the
honest prover ends with, that is (st, θ) for some θ, and the one lookup claim holds there of the
same entries. -/
def shiftQ_run : Prop :=
  ∀ (St J : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E)), P.Tags →
    ∀ (st : St) (y : Ex.Str) (m : J → E) (c : (P.bk Unit (J → E) Unit Ex).H.Coin)
        (ρ : Rho (P.bk Unit (J → E) Unit Ex).R.shape),
      P.inC st m →
      (P.bk Unit (J → E) Unit Ex).R.out st y (((P.bk Unit (J → E) Unit Ex).H.strat (m, ()) st c).run
          ρ).1 =
        some (((P.bk Unit (J → E) Unit Ex).H.strat (m, ()) st c).run ρ).2.1 ∧
      (((P.bk Unit (J → E) Unit Ex).H.strat (m, ()) st c).run ρ).2.1.1 = st ∧
      P.lk.inR (((P.bk Unit (J → E) Unit Ex).H.strat (m, ()) st c).run ρ).2.1 m

end
end Cb.Spec

namespace Cb
open Finset Prob Cb.Lkp Cb.LdLkp Iop IOR

section
variable (E : Type) [Field E] [Fintype E]

theorem shiftQ_lk : Spec.shiftQ_lk E := by
  intro St J M Wp Kc Ex P Mu R0 msg hT hMu
  unfold BkA.Good
  refine goodAt_draw Kc M St (St × E) Ex Wp E Prod.mk ((P.on msg).jIn R0) _ (2 ^ P.d) ?_
    (fun _ _ _ h => h) (fun _ => rfl) ?_
  · intro x y w θ h
    have ho : (P.on msg).outC (x, θ) w.1 := shiftQ_fwd E P.v P.d P.fK P.fT _ _ P.tag θ h.2
    exact ⟨h.1, ⟨ho, trivial⟩, hMu (x, θ) y w h.1 ho⟩
  · intro x y m _
    by_cases hin : (P.on msg).inC x m
    · refine le_trans (le_of_eq (cnt_false ?_)) (Nat.zero_le _)
      rintro θ ⟨wp, h, hn⟩
      exact hn ⟨h.1, hin⟩
    · refine (cnt_mono ?_).trans
        (shiftQ_cnt E P.v P.d P.fK P.fT (P.key x (msg m)) (P.tab x) P.tag (hT x) hin)
      rintro θ ⟨wp, h, _⟩
      exact h.2.1

theorem shiftQ_before : Spec.shiftQ_before E := by
  intro St J M Wp Kc Xo Ex P Mu R0 msg several b C hOk hMu hb
  cases several with
  | true =>
    exact segT_seq (shiftQ_lk E St J M Wp Kc Ex P Mu R0 msg hOk
      fun x y w => hMu x y w (fun h => absurd h (by simp))) hb
  | false =>
    have h1 := shiftQ_one E St M (P.on msg) hOk
    unfold BkA.Good at hb ⊢
    refine goodAt_preMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ (fun st => (st, (0 : E))) ?_ ?_ ?_ ?_
        hb
    · intro x y w h
      have ho : (P.on msg).outC (x, 0) w.1 := (h1 x w.1 0).2 h.2
      exact ⟨h.1, ⟨ho, trivial⟩, hMu (x, 0) y w (fun _ => rfl) h.1 ho⟩
    · exact fun _ _ h => h
    · exact fun _ => rfl
    · intro x y w _ h
      exact ⟨h.1, (h1 x w.1 0).1 h.2.1⟩

theorem shiftQ_asm2_base : Spec.shiftQ_asm2_base E := by
  intro p _ St A0 P Mu Ex Kc M Wp R0 msg several hOk hv hd hMu hA hM
  have g := ldLkpAsm2_base E p (P.asm A0) Mu Ex Kc M Wp (ShiftQ.ride R0) msg hA hM
  have e : (P.asm A0).lk = P.lk := by
    show (⟨A0.v' + 1, A0.d, _, _, _⟩ : Lk E (St × E) (A0.J → E)) = ⟨P.v, P.d, _, _, _⟩
    rw [hv, hd]
    rfl
  refine shiftQ_before E St A0.J M Wp Kc _ Ex P Mu R0 msg several _ _ hOk hMu ?_
  rw [← e]
  exact g

theorem shiftQ_ll : Spec.shiftQ_ll E := fun _ _ _ Wp _ _ Ex P _ _ _ h =>
  ⟨ll_seq (ll_draw Ex Wp E Prod.mk (2 ^ P.d)) h, ll_preM h _⟩

theorem shiftQ_run : Spec.shiftQ_run E := by
  intro St J Ex P hT st y m c ρ h
  have g := shiftQ_lk E St J (J → E) Unit Unit Ex P (fun _ _ => True)
    (⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, fun _ => ()⟩ :
      Rels Unit St Ex ((J → E) × Unit)) (fun m => m) hT fun _ _ _ _ _ => trivial
  have hfree : ρ ∉ (P.bk Unit (J → E) Unit Ex).H.withheld (m, ()) st := by
    have e : (P.bk Unit (J → E) Unit Ex).H.withheld (m, ()) st = ∅ :=
      (plain_draw E Prod.mk (2 ^ P.d) : (P.bk Unit (J → E) Unit Ex).Plain).free (m, ()) st
    rw [e]
    exact Set.notMem_empty _
  obtain ⟨h1, h2⟩ := g.acc st y (m, ()) c ρ ⟨trivial, h⟩ hfree
  have hs := g.same (m, ()) st c ρ
  refine ⟨h1, rfl, ?_⟩
  have h3 := h2.2.1
  rw [hs] at h3
  exact h3

end
end Cb
