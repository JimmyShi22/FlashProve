-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Shift/ShiftK.lean.
The shift that joins the lookups of several calls into one, as a block with knowledge soundness
alone, and laid before the whole lookup.

Several calls, each with its own key vector and table, are looked up at once. The joint vectors are
given as they lie, with two maps that say to which call an index belongs (`ShiftQ`). The verifier
draws theta and adds to each key and each row theta times the tag of its call: a key outside its own
call's table then meets the joint table for at most as many theta as that table has rows. With one
call nothing is drawn, and theta is 0.

Definitions. `P.bkK Ex`: the draw of theta with its count 2 ^ P.d, as a block without an honest
side. `P.lkK several b`: the draw and then the block b, or, with one call, b behind the map st ↦
(st, 0), without a round. `P.allK A0 several V VC`: that with b the whole lookup at the shifted
vectors, for two short sumcheck blocks V, VC.

Statements.
 * `shiftK_knowAt`, `shiftK_know`: the draw, from "each key is a row of its own call" to "each
   shifted key is a row of the shifted joint table"; the second with condition, two relations,
   extractor and errors written out.
 * `shiftK_lk`, `shiftK_before`, `shiftK_know0`: the same into the joint of any block that proves
   the one lookup claim, for both cases; the joint's exact side is a free letter, which knowledge
   soundness does not read.
 * `allK_base`, `allK_know`, `allK_know_sig`: the shift and the whole lookup as one reduction, from
   "each key is a row of its own call" to the claim on the joint keys and the rows; in the form
   `KnowAt`, written out, and over a signature.
 * `portK_know`: at the maps of a forest of calls (`OnBytes.Model.Forest.Shape`), from "each call's
   keys lie in that call's table".
Premises: `P.Tags` where theta is drawn, "all indices are of one call" where it is not (together
`P.Ok several`); for the whole lookup the conditions on its sizes; in `shiftK_before` and
`shiftK_know0` the knowledge soundness of b. The others speak of public numbers, maps, tags and
tables; none reads the committed messages, a witness or a transcript.

Not claimed here: anything about an honest prover; that the record A0 belongs to the forest; what
the short sumcheck blocks put out.

-/
import OnBytes.Tie.Pv.Lookup.Shift.ShiftQLay
import OnBytes.Tie.Pv.Lookup.Port.ShiftQPort
import Cb.Pv.Lookup.Know.AsmKV

set_option autoImplicit false

namespace Cb.LdLkp
open Finset Cb.Lkp Iop IOR Kn TWhole

namespace ShiftQ
variable {E St J : Type} [Field E] [Fintype E]

/-- The shift's block: the verifier's side and its error. -/
def bkK (P : ShiftQ E St (J → E)) (Ex : ExtSpec) : BkK St (St × E) Ex :=
  drawK E (Prod.mk : St → E → St × E) Ex (2 ^ P.d)

/-- The shift, if there are several calls, then the block b. -/
noncomputable def lkK (P : ShiftQ E St (J → E)) {Xo : Type} {Ex : ExtSpec} (several : Bool)
    (b : BkK (St × E) Xo Ex) : BkK St Xo Ex :=
  match several with
  | true => (P.bkK Ex).seq b
  | false => b.preM fun st => (st, (0 : E))

/-- The shift, then the whole lookup: the verifier and its errors, at two short sumcheck blocks. -/
noncomputable def allK (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E)) (several : Bool)
    (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) {Ex : ExtSpec} :
    BkK St (TX (P.asmH A0).St E (P.asmH A0).J) Ex :=
  P.lkK several ((P.asmH A0).baseK V VC)

end ShiftQ
end Cb.LdLkp

namespace Cb
open Finset Prob Cb.Lkp Cb.LdLkp Cb.LdLkp.Kn Iop IOR TWhole

section
variable (E : Type) [Field E] [Fintype E]

/-- The count at the draw, in the form that a draw's Know asks. -/
theorem shiftK_cnt (St J M Wp Kc : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E))
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) (hT : P.Tags) (x : St) (y : Ex.Str) (m : M) :
    cnt (fun θ : E => ∃ wp, (R0.relR (x, y) (m, wp) ∧ (P.on msg).outC (x, θ) m) ∧
      ¬ (R0.relR (x, y) (m, wp) ∧ (P.on msg).inC x m)) ≤ 2 ^ P.d := by
  by_cases hin : (P.on msg).inC x m
  · refine le_trans (le_of_eq (cnt_false ?_)) (Nat.zero_le _)
    rintro θ ⟨wp, h, hn⟩
    exact hn ⟨h.1, hin⟩
  · refine (cnt_mono ?_).trans
      (shiftQ_cnt E P.v P.d P.fK P.fT (P.key x (msg m)) (P.tab x) P.tag (hT x) hin)
    rintro θ ⟨wp, h, _⟩
    exact h.2

/-- The draw, between the shift's own joints. -/
theorem shiftK_knowAt (St J M Wp Kc : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E))
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) (hT : P.Tags) :
    (P.bkK Ex).Know ((P.on msg).jIn R0) ((P.on msg).jOut R0) :=
  knowAt_draw Kc M St (St × E) Ex Wp E Prod.mk ((P.on msg).jIn R0) ((P.on msg).jOut R0) (2 ^ P.d)
    (fun _ _ _ h => h) fun x y m _ => shiftK_cnt E St J M Wp Kc Ex P R0 msg hT x y m

/-- Several calls: one draw. Condition, relations, extractor and errors written out. -/
theorem shiftK_know (St J M Wp Kc : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E))
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) (hT : P.Tags) (m : M) :
    (P.bkK Ex).R.red.Know R0.on
      (fun a wp => R0.relR a (m, wp) ∧ AllInQ P.v P.d P.fK P.fT (P.key a.1 (msg m)) (P.tab a.1))
      (fun b wp => R0.relR (b.1.1, b.2) (m, wp) ∧
        InTable P.v P.d (shKeyQ P.fK (P.key b.1.1 (msg m)) P.tag b.1.2)
          (shTabQ P.fT (P.tab b.1.1) P.tag b.1.2))
      (fun _ _ wp => wp) ((2 ^ P.d, ()) : ℕ × Unit) :=
  (shiftK_knowAt E St J M Wp Kc Ex P R0 msg hT).know m

/-- The draw, into the in-joint of a lookup's block. Φ, the joint's exact side, is any: KnowAt does
not read it. -/
theorem shiftK_lk (St J M Wp Kc : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E))
    (Φ : St × E → (J → E) → Prop) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) (hT : P.Tags) :
    (P.bkK Ex).Know ((P.on msg).jIn R0) (cj (ShiftQ.ride R0) msg id Φ P.lk.inR) :=
  knowAt_draw Kc M St (St × E) Ex Wp E Prod.mk ((P.on msg).jIn R0) _ (2 ^ P.d)
    (fun _ _ _ h => h) fun x y m _ =>
      (cnt_mono fun _ ⟨wp, h, hn⟩ => ⟨wp, ⟨h.1, h.2.1⟩, hn⟩).trans
        (shiftK_cnt E St J M Wp Kc Ex P R0 msg hT x y m)

/-- Before ANY block that proves the one lookup claim: for both values of several. -/
theorem shiftK_before (St J M Wp Kc Xo : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E))
    (Φ : St × E → (J → E) → Prop) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) (several : Bool)
    (b : BkK (St × E) Xo Ex) (C : Rels Kc Xo Ex (M × Wp)) (hOk : P.Ok several)
    (hb : b.Know (cj (ShiftQ.ride R0) msg id Φ P.lk.inR) C) :
    (P.lkK several b).Know ((P.on msg).jIn R0) C := by
  cases several with
  | true => exact know_seq (shiftK_lk E St J M Wp Kc Ex P Φ R0 msg hOk) hb
  | false =>
    have h1 := shiftQ_one E St M (P.on msg) hOk
    refine know_preM (fun st => (st, (0 : E))) (fun _ _ h => h) ?_ hb
    intro x y w _ h
    exact ⟨h.1, (h1 x w.1 0).1 h.2.1⟩

/-- One call: no round. Written out, for any block b behind the map st ↦ (st, 0) and any joint
behind b. -/
theorem shiftK_know0 (St J M Wp Kc Xo : Type) (Ex : ExtSpec) (P : ShiftQ E St (J → E))
    (R0 : Rels Kc St Ex (M × Wp)) (msg : M → J → E) (b : BkK (St × E) Xo Ex)
    (C : Rels Kc Xo Ex (M × Wp)) (h1 : ∀ X < 2 ^ P.v, ∀ Y < 2 ^ P.d, P.fT Y = P.fK X)
    (hb : b.Know (cj (ShiftQ.ride R0) msg id (fun _ _ => True) P.lk.inR) C) (m : M) :
    (b.preM fun st => (st, (0 : E))).R.red.Know R0.on
      (fun a wp => R0.relR a (m, wp) ∧ AllInQ P.v P.d P.fK P.fT (P.key a.1 (msg m)) (P.tab a.1))
      (fun c wp => C.relR c (m, wp)) (fun _ _ wp => wp) b.e :=
  (shiftK_before E St J M Wp Kc Xo Ex P (fun _ _ => True) R0 msg false b C h1 hb).know m

/-- The lookup claim of the assembly at the shifted vectors is the shift's own. -/
theorem asmH_lk (St : Type) (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E)) (hv : P.v = A0.v' + 1)
    (hd : P.d = A0.d) : (P.asmH A0).lk = P.lk := by
  show (⟨A0.v' + 1, A0.d, _, _, _⟩ : Lk E (St × E) (A0.J → E)) = ⟨P.v, P.d, _, _, _⟩
  rw [hv, hd]
  rfl

/-- The shift, then the whole lookup, in the form `KnowAt`. -/
theorem allK_base (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E))
    (several : Bool) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → A0.J → E)
    (hOk : P.Ok several) (hv : P.v = A0.v' + 1) (hd : P.d = A0.d) (hA : A0.H.lkb.Adm p)
    (hP : padsOK (A0.v' + 1) A0.d A0.pads = true) (hF : A0.n + 1 + 1 = 2 ^ A0.w) :
    (P.allK A0 several V VC).Know ((P.on msg).jIn R0)
      (cj (ShiftQ.ride R0) msg Prod.fst ((P.asmH A0).lk.out id id) ((P.asmH A0).lk.out id id)) := by
  have g := asmK_base E p (P.asmH A0) (fun _ _ => True) Ex Kc M Wp (PscLtK.ofShort V VC Ex)
    (ShiftQ.ride R0) msg (asmK_shortOK E (P.asmH A0) V VC Ex M Wp Kc msg) hA hP hF
  rw [asmH_lk E St A0 P hv hd] at g
  rw [asmH_lk E St A0 P hv hd]
  exact shiftK_before E St A0.J M Wp Kc _ Ex P (P.lk.inP fun _ _ => True) R0 msg several _ _ hOk g

/-- One reduction, written out: from "each key is a row of its own call's table" to the claim on the
joint keys and the rows. -/
theorem allK_know (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E))
    (several : Bool) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → A0.J → E)
    (hOk : P.Ok several) (hv : P.v = A0.v' + 1) (hd : P.d = A0.d) (hA : A0.H.lkb.Adm p)
    (hP : padsOK (A0.v' + 1) A0.d A0.pads = true) (hF : A0.n + 1 + 1 = 2 ^ A0.w) (m : M) :
    (P.allK A0 several V VC).R.red.Know R0.on
      (fun a wp => R0.relR a (m, wp) ∧ AllInQ P.v P.d P.fK P.fT (P.key a.1 (msg m)) (P.tab a.1))
      (fun b wp => R0.relR (b.1.1.1, b.2) (m, wp) ∧ (P.asmH A0).lk.out id id b.1 (msg m))
      (fun _ _ wp => wp) (P.allK A0 several V VC).e :=
  (allK_base E p St A0 P several V VC Ex Kc M Wp R0 msg hOk hv hd hA hP hF).know m

/-- Over a signature, by the library's sigLift_know. -/
theorem allK_know_sig (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E) (P : ShiftQ E St (A0.J → E))
    (several : Bool) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Sg : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (R0 : Rels Kc St E₀ (Sg.Msg × Wp))
    (msg : Sg.Msg → A0.J → E)
    (hOk : P.Ok several) (hv : P.v = A0.v' + 1) (hd : P.d = A0.d) (hA : A0.H.lkb.Adm p)
    (hP : padsOK (A0.v' + 1) A0.d A0.pads = true) (hF : A0.n + 1 + 1 = 2 ^ A0.w) :
    ((P.allK A0 several V VC).R.keep Sg.Smp Sg.ext).red.Know
      (Sg.over ((P.on msg).jIn R0)).on
      (Sg.over ((P.on msg).jIn R0)).relR
      (Sg.over (cj (ShiftQ.ride R0) msg Prod.fst ((P.asmH A0).lk.out id id)
        ((P.asmH A0).lk.out id id))).relR
      (fun _ _ w => (w.1, w.2)) (P.allK A0 several V VC).e :=
  sigLift_know E Sg Kc _ _ Wp Wp E₀ E₀ (P.allK A0 several V VC).R _ _ (fun _ _ _ wp => wp)
    (P.allK A0 several V VC).e
    (allK_base E p St A0 P several V VC E₀ Kc Sg.Msg Wp R0 msg hOk hv hd hA hP hF).know

/-- At the maps of a forest of calls, written out: from "each call's keys lie in that call's table".
-/
theorem portK_know (p : ℕ) [CharP E p] (St : Type) (A0 : LkAsmH E) (h : Port.Sh)
    (T : St → ℕ → ℕ → E) (K : St → (A0.J → E) → ℕ → ℕ → E)
    (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex) (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex)
    (Ex : ExtSpec) (Kc M Wp : Type) (R0 : Rels Kc St Ex (M × Wp)) (msg : M → A0.J → E)
    (hOK : Port.OK h) (hp : h.NC ≤ p) (hv : h.v = A0.v' + 1) (hd : h.d = A0.d)
    (hA : A0.H.lkb.Adm p) (hP : padsOK (A0.v' + 1) A0.d A0.pads = true)
    (hF : A0.n + 1 + 1 = 2 ^ A0.w) (m : M) :
    ((Port.Q h T K).allK A0 (Port.several h) V VC).R.red.Know R0.on
      (fun a wp => R0.relR a (m, wp) ∧
        ∀ c < h.NC, InTable (Port.nOf h c) (Port.kOf h c) (K a.1 (msg m) c) (T a.1 c))
      (fun b wp => R0.relR (b.1.1.1, b.2) (m, wp) ∧
        ((Port.Q h T K).asmH A0).lk.out id id b.1 (msg m))
      (fun _ _ wp => wp) ((Port.Q h T K).allK A0 (Port.several h) V VC).e :=
  (allK_know E p St A0 (Port.Q h T K) (Port.several h) V VC Ex Kc M Wp R0 msg
    (port_ok E p St A0.J h T K hOK hp) hv hd hA hP hF m).conseq (fun _ h => h)
    (fun a _ _ hw => ⟨hw.1, (port_in_iff E h (T a.1) (K a.1 (msg m)) hOK).1 hw.2⟩) fun _ _ h => h

end
end Cb
