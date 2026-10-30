-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05TiePublic.lean: kind K5: ALL THAT THE TIE BETWEEN THE LAW's WORLD AND THE
TABLE OF JOINTS' ASKS OF PUBLIC DATA, BUT FOR THE TABLE's LIST OF MEMBERS, AS ONE BOOL WITH CODE;
and the law's premise on the forms' worth (billsWorthJ_table,
Johnson/Desc/First/Att/K05WorthAtFuns.lean) under that Bool.

IS IT EMPTY HERE? NO MEMBER IS SHOWN: the Bool is evaluated nowhere in this library. D : Sent IS
BUILT NOWHERE in this library. On the form of hRd and hbehind, and on Returns' field u3: the face
of K05WorthAtFuns.lean.

Main names:
  `oneMaskB D i`: a Bool: the member that holds link i's mask row has one mask row. `hone_of_B`.
  `tiePublicB D x tl hi`: **FIVE BOOLS**: Codes.lengthsOk D.codes · reqLayoutOk D.codes D.shape
    D.layout · symArraysB D x tl (Johnson/Desc/First/Att/K05SymsOf.lean) · masksUpTo D x hi
    (Johnson/Desc/First/Att/K05MasksAtt.lean) · oneMaskB D x.link. None reads a radius, a record, a
    message or a witness; none walks over the symbols.
  `TiePub D x tl hi rad`: the four facts that are spent: SymsOK, masksUpTo, reqLayoutOk and hone.
  `tiePublic_gives`: a yes of tiePublicB gives TiePub, at every rad. (Other payers: SymsOK from the
    lookup argument's test readsB,
    Johnson/Desc/First/Att/K05SymsOfReads.lean [not in this library]; the other
    three from a return of buildLinksH, Johnson/Desc/First/Att/K05PublicOfBuilt.lean.)
  `billsWorthJ_public`: **billsWorthJ_table with its public premises := TiePub and MemAt**; ps and
    qs are the pairs at the members that are read (psOf, qsOf, readMsgs,
    Johnson/Desc/First/Att/K05ReadMsgs.lean): hcov and hcovM are paid.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05WorthAtFuns
import Johnson.Desc.First.Att.K05SymsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Params
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.K9 (Readers segAt?)
open VerifiableInference.Desc.Sound (Stated Mem msgsOf MsgT seatTab formsTQ)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open K5Law (funsAt)

/-- The member that holds the mask row has one mask row. -/
def oneMaskB (D : Sent) (i : ℕ) : Bool :=
  (maskMsg D i).all fun k => ((shapesCalls D i)[k]?).all fun o => o.maskRows == 1

theorem hone_of_B {D : Sent} {i : ℕ} (h : oneMaskB D i = true) (rad : OracleShape → Nat) (k : ℕ)
    (hk : k < (sigListCalls D rad i).length) (hm : maskMsg D i = some k) :
    ((sigListCalls D rad i).get ⟨k, hk⟩).1.maskRows = 1 := by
  unfold oneMaskB at h
  rw [hm] at h
  have e : (shapesCalls D i)[k]? = some ((sigListCalls D rad i).get ⟨k, hk⟩).1 := by
    rw [← shapes_any D rad i, List.getElem?_map, List.getElem?_eq_getElem hk]
    rfl
  simp only [Option.all_some] at h
  rw [e] at h
  simpa using h

/-- **What the tie asks of public data**, as four facts: every symbol address has a seat that lies
in its table, and a kept message has its source's shape (SymsOK) · every mask entry below hi has a
seat · the layout is lawful · the member that holds the link's mask row has one mask row. -/
def TiePub (D : Sent) (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (hi : ℕ)
    (rad : OracleShape → Nat) : Prop :=
  SymsOK x tl D rad ∧ masksUpTo D x hi = true ∧ reqLayoutOk D.codes D.shape D.layout = true ∧
    ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1

/-- **All that the tie asks of public data, but for the table's list of members.** -/
def tiePublicB (D : Sent) (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (hi : ℕ) :
    Bool :=
  D.codes.lengthsOk && reqLayoutOk D.codes D.shape D.layout && symArraysB D x tl &&
    masksUpTo D x hi && oneMaskB D x.link

theorem tiePublic_gives {D : Sent} {x : VerifiableInference.Desc.First.Look.Place} {tl : HTailF2}
    {hi : ℕ} (h : tiePublicB D x tl hi = true) (rad : OracleShape → Nat) : TiePub D x tl hi rad := by
  unfold tiePublicB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨symsOK_of_layout h1 h2 h3, h4, h2, hone_of_B h5 rad⟩

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

/-- **The law's premise on the forms' worth, with its public premises := one Bool and MemAt.** -/
theorem billsWorthJ_public {Y : Type} (ns : ℕ) (N : Nums) (A0 : Attention.Plan) (k3 : Runs.PadIn)
    (tj : OnBytes.K.Kc.Tape) (gOf : First.S × Y → Forest.Heard) (xr : Params.AttentionRounds)
    (on : First.S × Y → Prop) (R' : First.S × Y → Wit Cells Tok MsgT → Prop) (Rds : ℕ → Readers)
    (runs : ℕ → ℕ → String → List (ℕ × String))
    (St : Stated) (Nn : Numbers)
    (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem)
    (hi : ℕ) (hpub : TiePub D x A.seam.tl hi rad)
    (r1 : (2, "first") ∈ runs x.link 3 "own") (r2 : (2, "second") ∈ runs x.link 3 "own")
    (r3 : (2, "join") ∈ runs x.link 2 "join")
    (hitems : ∀ b w, R' b w →
      (∀ p ∈ runs x.link 3 "own", formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arr ms w)) ∧
      ∀ p ∈ runs x.link 2 "join", formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 b.1 (seatTab D.codes arr ms w))
    (hRd : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∃ R₁ R₂ R₃ : VerifiableInference.Desc.K9.Read,
          (Rds x.link).forms 2 "first" b.1 = some R₁ ∧ R₁.late = [] ∧ (∀ f ∈ l₁, f ∈ R₁.forms) ∧
          (Rds x.link).forms 2 "second" b.1 = some R₂ ∧ R₂.late = [] ∧ (∀ f ∈ l₂, f ∈ R₂.forms) ∧
          (Rds x.link).forms 2 "join" b.1 = some R₃ ∧ R₃.late = [] ∧ xj.1 ∈ R₃.forms)
    (hm : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    (hfront : ∀ a : First.S × Y, on a →
      (∃ L, FrontFacts x A D (Nn.sent x.link 0)
        (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
        (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) a.1 L) ∧
      ∀ a₀, a.1.here = .att a₀ → ∃ g, a₀.g = some g ∧ SeatReadsSame g (gOf a))
    (hbehind : ∀ (a b : First.S × Y) (w : Wit Cells Tok MsgT), on a → R' b w →
      ∀ (F G : Fork) (h : Heard) (Ls : Lists),
      seatSO.ledger a.1 = some F → seatSO.lay a.1 h G = some b.1 → Said xr h G Ls → Stays F G →
      G.ns = F.ns →
      ∀ (l : Left) (i : Runs.In) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (kf : Array Aff)
        (xj : Aff × Fork × OnBytes.K.Kc.Tape),
        Returns A.S (gOf a).zx (gOf a).zk G h l A0 (gOf a) i (plannedK A) l₁ l₂ jn k3 kf G tj xj
          A.seam.tl A.nW (lookOfO (parCOf A).geo.lmb (gOf a)) →
        ∀ (pt : VerifiableInference.Desc.K9.Part) (L : LinkCtx), segAt? b.1 = some pt →
          a.1.link? = some L →
          BehindFacts A hi b.1 L pt (l₁ ++ l₂ ++ [xj.1]) ∧ (G.trees[A.iU3]?).isSome = true) :
    BillsWorthJ x A.seam.tl D rad Ex Wp α A.S ns N A0 (plannedK A) k3 A.nW tj gOf
      (fun a => lookOfO (parCOf A).geo.lmb (gOf a)) seatSO xr
      (fun a : First.S × Y => a.1) (fun a : First.S × Y => a.1) on
      (fun w => msgsOf D.codes (sigListCalls D rad x.link) seat arr w) R' := by
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  exact billsWorthJ_table x A D rad Ex Wp α ns N A0 k3 tj gOf xr on R' Rds runs St Nn x.link
    arr seat ms hi _ _ r1 r2 r3 hitems hRd p1 p2 p3 p4 hm
    (hcov_of D rad x A.seam.tl seat) (hcovM_of D rad x A.seam.tl) hSt hfront hbehind

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.hone_of_B
#print axioms VerifiableInference.Desc.First.Att.P.tiePublic_gives
#print axioms VerifiableInference.Desc.First.Att.P.billsWorthJ_public
