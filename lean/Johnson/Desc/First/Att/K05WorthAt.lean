-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05WorthAt.lean: kind K5: THE LAW's PREMISE ON THE FORMS' WORTH (BillsWorthJ,
Johnson/Desc/First/Att/K05BillsWorth.lean: the field worth of K5Behind) AT THE TABLE OF JOINTS' OWN
FILLING: the pieces put together, so that Lean holds that their letters fit:
billsWorthJ_of_formsT (Johnson/Desc/First/Att/K05WorthAtTable.lean), hTie_at
(Johnson/Desc/First/Att/K05WorldTieAt.lean), and THE SENTENCE of the table's item formsT, written
out: at every run p that the item names: formsTQ (Rd m) St (N.sent m 0) p.1 p.2 s (seatTab cs arr ms
w). (The function meaningForms, Johnson/Desc/Sound/BordersForms.lean,
is named in no statement: three texts of that file stand; at each the sentence is the
item's filling, or its first conjunct.)

IS IT EMPTY HERE? NO MEMBER IS SHOWN. A CARRIAGE BETWEEN TWO WORLDS, NO PAYMENT.

Main names:
  `formsT_gives`: where the filled items formsT m 3 "own" and formsT m 2 "join" hold of a witness,
    and the table's names stand for the driver's pairs (2, "first"), (2, "second") and (2, "join"),
    the three sentences formsTQ hold at these pairs: the premise hR'. (Called in
    Johnson/Desc/First/Att/K05WorthAtFuns.lean: billsWorthJ_table; billsWorthJ_at takes hR' as a
    premise.)
  `billsWorthJ_at`: **BillsWorthJ at the law's letters**: part := the typed messages of the witness,
    R' := any relation behind that holds the two filled items: from hRd (the reader's three lists
    hold the returned forms, no late slot), and the premises of hTie_at.
Limits. A rule over letters. hRd, the public facts, StatedAtt and hrec are premises: who pays each
stands on the faces of the files named.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05WorldTieAt
import Johnson.Desc.Sound.BordersForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.K9 (Readers segAt?)
open VerifiableInference.Desc.Sound (Stated Mem seatTab msgsOf MsgT formsTQ)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open K5Law (oldOf)

section
variable {Cells Tok : Type}

/-- **The premise hR', from the table's own filling of formsT.** -/
theorem formsT_gives (cs : Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Rd : ℕ → Readers)
    (runs : ℕ → ℕ → String → List (ℕ × String)) (St : Stated)
    (N : Numbers) (m : ℕ) (s : First.S) (w : Wit Cells Tok MsgT)
    (r1 : (2, "first") ∈ runs m 3 "own") (r2 : (2, "second") ∈ runs m 3 "own")
    (r3 : (2, "join") ∈ runs m 2 "join")
    (h1 : ∀ p ∈ runs m 3 "own", formsTQ (Rd m) St (N.sent m 0) p.1 p.2 s (seatTab cs arr ms w))
    (h2 : ∀ p ∈ runs m 2 "join", formsTQ (Rd m) St (N.sent m 0) p.1 p.2 s (seatTab cs arr ms w)) :
    formsTQ (Rd m) St (N.sent m 0) 2 "first" s (seatTab cs arr ms w) ∧
      formsTQ (Rd m) St (N.sent m 0) 2 "second" s (seatTab cs arr ms w) ∧
      formsTQ (Rd m) St (N.sent m 0) 2 "join" s (seatTab cs arr ms w) :=
  ⟨h1 _ r1, h1 _ r2, h2 _ r3⟩

variable (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

/-- **The law's premise on the forms' worth, at the witness and the stated function.** -/
theorem billsWorthJ_at {Y : Type} (ns : ℕ) (N : Nums) (A0 : Attention.Plan) (k3 : Runs.PadIn)
    (tj : OnBytes.K.Kc.Tape) (gOf : First.S × Y → Forest.Heard) (xr : Params.AttentionRounds)
    (on : First.S × Y → Prop) (R' : First.S × Y → Wit Cells Tok MsgT → Prop) (Rd : Readers)
    (St : Stated) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape)) (fA : First.S → List HFun)
    (hR' : ∀ b w, R' b w → formsTQ Rd St own 2 "first" b.1 (seatTab D.codes arr ms w) ∧
      formsTQ Rd St own 2 "second" b.1 (seatTab D.codes arr ms w) ∧
      formsTQ Rd St own 2 "join" b.1 (seatTab D.codes arr ms w))
    (hRd : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∃ R₁ R₂ R₃ : VerifiableInference.Desc.K9.Read,
          Rd.forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          Rd.forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          Rd.forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms)
    (hR : SymsOK x A.seam.tl D rad) (hmk : masksUpTo D x hi = true)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hcov : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link → StatedAtt St A fA s)
    (hrec : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∀ pt : VerifiableInference.Desc.K9.Part, segAt? b.1 = some pt →
          (∃ L, TieFacts x A D rad own ps qs hi b.1 L pt (l₁ ++ l₂ ++ [xj.1])) ∧
            fA b.1 = (oldOf A.S (gOf a) i).t.funs.toList) :
    BillsWorthJ x A.seam.tl D rad Ex Wp α A.S ns N A0 (plannedK A) k3 A.nW tj gOf
      (fun a => lookOfO (parCOf A).geo.lmb (gOf a)) seatSO xr
      (fun a : First.S × Y => a.1) (fun a : First.S × Y => a.1) on
      (fun w => msgsOf D.codes (sigListCalls D rad x.link) seat arr w) R' :=
  billsWorthJ_of_formsT x A.seam.tl D rad Ex Wp α A.S ns N A0 (plannedK A) k3 A.nW tj gOf _ xr on _ R'
    Rd St own (fun w => seatTab D.codes arr ms w) hR' hRd
    (hTie_at x A D rad Ex Wp α ns N A0 k3 tj gOf xr on R' Rd St own arr seat ms hi ps qs fA hR hmk hone
      hm hcov hcovM hSt hR' hRd hrec)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.formsT_gives
#print axioms VerifiableInference.Desc.First.Att.P.billsWorthJ_at
