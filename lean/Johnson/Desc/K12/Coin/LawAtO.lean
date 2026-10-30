-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- Typed against the files of Johnson/Desc/K12/Coin/ (PaidByPlan.lean among them), Law/DataOf.lean and Law/DataO.lean.
/-
Johnson/Desc/K12/Coin/LawAtO.lean: THE PROXIMITY TEST's LAW, SECOND ARM (k12_lawRecFreeO, Coin/FreeOff.lean), CALLED AT ONE CLOSED INSTANCE. THE OBJECT IS pieceT … (proximityTestKind guardedProximityTestParts piO) AT ITS OWN RECORD, OVER A FRAME AND DATA MADE BY HAND OFF THE PLAN: NOT THE PIECE OF A DESCRIPTION's TILING; THE SECOND ARM IS SEATED NOWHERE. FOR THE ONE BASE.
(Where this and lean/THEOREM.md differ,
the page holds.) NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  The place: the proximity test O (the own-mask place) of the SMALL stored proof of a build not in this repository: piO (Law/PlacesSmall.lean), record tO (Law/LitO.lean).
  THE LETTERS, CLOSED: num := numAt t₁ t₂ 1 · no := fun z => t₁ + z · base := t₁ + 5 · n := 5 (promise_O's) · lstJ · flC · flZ · flZ · rad := fun s => rO s.st · v₀ := 768 · frO t₁ key := ⟨0, allO t₁, key, 0⟩ (eight trees: the record's book's five and the three that the test sends, with their depths) · dBO :: dtO := piO's written rounds with their declared openings by num (Law/DataOf.lean) · εO := the chain's own counts (bears_own's choice), cO the place's chain.
  FREE ON PURPOSE: t₁ (how many trees the first chain sends) · t₂ (idle) · key (which key the true file has is said by nobody) · W · rd · the oracles y.
  wants_dataOf: the lemma on lists for the field wants. len_like: a chain's shape and a like stretch's are as long.
  atPlaceOwn_O: AtPlaceOwn, ALL THIRTEEN FIELDS, no premise.
  law_O: the law called. law_O_at: the law at (tO, y), whatever the oracles y: by promise_O (Coin/MemberProm.lean).
  counts_O: εO's numbers ARE the chain's own. below_like: «Below» goes from a chain's rounds to a stretch that is like its written rounds. small_O: every count of εO is at most 2⁻¹ ^ 128 of its own round's verifier messages, in the stretch's shape (from K12Condition at piO, Law/CondMembers.lean). bat_small_O: "BAT"'s own count 768 · w likewise, at the stretch's first round (batBelow_like, Law/BatValsPayAt.lean).
WHAT IT IS NOT: A LAW CALLED, NOT A LAW SHOWN TO BITE: no (y, τ) with a yes of the piece is exhibited: at a wrong key the piece refuses all, and «Doomed (a yes ⇒ QN)» is then true for nothing. No sentence on bits of security follows from small_O. That tO is the record which the verifier reaches on the stored file is a run's word.

-/
import Johnson.Desc.K12.Coin.FreeOff
import Johnson.Desc.K12.Coin.MemberProm
import Johnson.Desc.K12.Coin.BearsOwn
import Johnson.Desc.K12.Coin.PaidByPlan
import Johnson.Desc.K12.Law.DataO
import Johnson.Desc.K12.Law.CondMembers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple PayRec)
open H2K.Pub (WR sgOf writtenOf chainFrom)
open H2K.Member (piO tO rO rdtOf dataOf like_dataOf flat_of rdsO wsO r0O rtO w0O lO aO restO stages_O
  wsO_cons rdsO_cons written_O len_O stored_O allO stO data_O depth_O cO cO_eq cO_rds ds_O log_O
  payPub_O member_O)

/-- The maker's wants at data made off declared rounds are the declared rounds' wants. -/
theorem wants_dataOf (a : ℕ) (dep : ℕ → Option ℕ) (num : Fmt.TreeSource → ℕ) :
    ∀ (ws : List WR) (rs : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ r ∈ rs, r.stored = []) → (∀ r ∈ rs, ∀ o ∈ r.opens, dep (num o.2) = some o.1.a) →
    ws.length = rs.length → wantsOf a dep (dataOf num ws rs) Rs = wantsDecl num rs Rs
  | [], [], _, _, _, _ => by simp [H2K.Member.dataOf, wantsOf, wantsDecl]
  | _ :: _, _ :: _, [], _, _, _ => by simp [H2K.Member.dataOf, wantsOf, wantsDecl]
  | w :: ws, r :: rs, R :: Rs, hst, hdep, hl => by
    have ih := wants_dataOf a dep num ws rs Rs (fun r' h' => hst r' (List.mem_cons_of_mem _ h'))
      (fun r' h' => hdep r' (List.mem_cons_of_mem _ h')) (Nat.succ.inj hl)
    have e1 := hst r (List.mem_cons_self ..)
    show (([] : List Fmt.Stored).flatMap _ ++ ((r.opens.map fun o => num o.2).flatMap _) ++
      wantsOf a dep (dataOf num ws rs) Rs) = _
    rw [ih, flat_of _ (fun o => (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
      Want.tree (num o.2) x) num r.opens fun o ho => by
        simp only [hdep r (List.mem_cons_self ..) o ho]]
    simp only [wantsDecl, e1, List.flatMap_nil]
  | [], _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h

/-- A chain's shape and the shape of a stretch that is like its written rounds are as long. -/
theorem len_like (dt : List RDT) (l : List WR) (h : List.Forall₂ Like dt l) :
    (PQ.uL (ckP .two) (l.map WR.rd)).length = (uLT (ckP .two) dt).length := by
  obtain ⟨lo, rfl, h2⟩ := like_lo dt l h
  rw [← h2]
  have e := errList_errW (ckP .two) lo (errOfList _ [])
  have l1 := errList_length _ (errW (ckP .two) lo (errOfList _ []))
  have l2 := errList_length _ (errOfList (PQ.uL (ckP .two) (lo.map (·.1))) [])
  rw [e] at l1
  exact l2.symm.trans l1

/-! ## The letters -/

/-- No stored table (a := 0); all eight trees; ft := 0, which is piO.nums.firstTree. -/
def frO (t₁ : ℕ) (key : ℕ → ℕ) : Frame := ⟨0, allO t₁, key, 0⟩

theorem frO_ft (t₁ : ℕ) (key : ℕ → ℕ) : (frO t₁ key).ft = piO.nums.firstTree := rfl
def dBO (t₁ t₂ : ℕ) : RDT := rdtOf (numAt t₁ t₂ 1) w0O r0O
def dtO (t₁ t₂ : ℕ) : List RDT := dataOf (numAt t₁ t₂ 1) lO rtO

noncomputable def εO (t₁ t₂ : ℕ) : Err (uLT (ckP .two) (dtO t₁ t₂)) :=
  errOfList (uLT (ckP .two) (dtO t₁ t₂)) (errList _ cO.errL)

theorem num_own (t₁ t₂ n : ℕ) : numAt t₁ t₂ 1 (.own n) = t₁ + n := by simp [numAt]

theorem like_O (t₁ t₂ : ℕ) : List.Forall₂ Like (dtO t₁ t₂) lO :=
  like_dataOf (numAt t₁ t₂ 1) lO rtO len_O -- `like_dataOf` states the text of `Like`, unfolded

theorem len_cO (t₁ t₂ : ℕ) :
    (PQ.uL (ckP .two) cO.rds).length = (uLT (ckP .two) (dtO t₁ t₂)).length := by
  rw [cO_rds]
  exact len_like _ _ (like_O t₁ t₂)

/-- **AtPlaceOwn at piO: all thirteen fields, no premise.** -/
theorem atPlaceOwn_O (t₁ t₂ : ℕ) (key : ℕ → ℕ) :
    AtPlaceOwn (frO t₁ key) piO (numAt t₁ t₂ 1) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rO s.st)
      (t₁ + 5) (dBO t₁ t₂) (dtO t₁ t₂) (εO t₁ t₂) := by
  obtain ⟨_, _, hp, he, ha, ho, hj, _, hsp, _, _⟩ := member_O
  refine atPlaceOwn_of_plan (frO t₁ key) piO (numAt t₁ t₂ 1) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => rO s.st) (t₁ + 5) (dBO t₁ t₂) (dtO t₁ t₂) (εO t₁ t₂) he ha hp hsp
    (H2K.Pub.codes_of_johOk rO piO hj)
    ⟨w0O, lO, written_O, .cons ⟨rfl, rfl, rfl, rfl, rfl⟩ (like_O t₁ t₂)⟩ rfl ho ?_
    (numOwn_numAt t₁ t₂ 1 5 (t₁ + 5) (num_own t₁ t₂ 5))
    (bears_own piO Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => rO s.st) (dtO t₁ t₂) aO restO w0O lO cO
      stages_O written_O cO_eq (len_cO t₁ t₂))
  intro Rs
  have hl : wsO.length = rdsO.length := by
    rw [wsO_cons, rdsO_cons, List.length_cons, List.length_cons, len_O]
  have h := wants_dataOf 0 (stO (numAt t₁ t₂ 1) t₁ key).depth (numAt t₁ t₂ 1) wsO rdsO Rs stored_O
    (depth_O (numAt t₁ t₂ 1) t₁ key (num_own t₁ t₂)) hl
  rw [← data_O] at h
  show wantsOf 0 (stO (numAt t₁ t₂ 1) t₁ key).depth
    (rdtOf (numAt t₁ t₂ 1) w0O r0O :: dataOf (numAt t₁ t₂ 1) lO rtO) Rs = wantsDecl (numAt t₁ t₂ 1) rdsO Rs
  exact h

/-- **The law called.** By itself it says little of how great εO is: small_O (below) stands beside it
for that. -/
theorem law_O (t₁ t₂ : ℕ) (key : ℕ → ℕ) (W : Type) (rd : ℕ → ℕ) :
    (pieceT (frO t₁ key) W piO (t₁ + 5) (dBO t₁ t₂) (dtO t₁ t₂)
        (768 * (bsRound .two (dBO t₁ t₂).entry (dBO t₁ t₂).kind).w) (εO t₁ t₂)).ior.red.Leads
      (fun x => x.1.roots = 5 ∧
        (FirstOpensOwn piO (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 5) x.1 ∧ PayRec piO x.1))
      (fun x _ => QN piO (NTuple (frO t₁ key) piO (fun z => t₁ + z) (fun s => rO s.st) rd) x)
      (pieceT (frO t₁ key) W piO (t₁ + 5) (dBO t₁ t₂) (dtO t₁ t₂)
        (768 * (bsRound .two (dBO t₁ t₂).entry (dBO t₁ t₂).kind).w) (εO t₁ t₂)).err :=
  k12_lawRecFreeO (frO t₁ key) W piO (numAt t₁ t₂ 1) (fun z => t₁ + z) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => rO s.st) rd (t₁ + 5) (dBO t₁ t₂) (dtO t₁ t₂) 768 (εO t₁ t₂) 5 member_O.2.2.2.1
    member_O.2.2.1 (fun _ => atPlaceOwn_O t₁ t₂ key) payPub_O ds_O log_O

/-- **The law at the real record, whatever the oracles.** -/
theorem law_O_at (t₁ t₂ : ℕ) (key : ℕ → ℕ) (W : Type) (rd : ℕ → ℕ) (y : (frO t₁ key).E.Str) :
    Doomed _
      (pieceT (frO t₁ key) W piO (t₁ + 5) (dBO t₁ t₂) (dtO t₁ t₂)
        (768 * (bsRound .two (dBO t₁ t₂).entry (dBO t₁ t₂).kind).w) (εO t₁ t₂)).err
      (fun τ => ∀ b,
        (pieceT (frO t₁ key) W piO (t₁ + 5) (dBO t₁ t₂) (dtO t₁ t₂)
          (768 * (bsRound .two (dBO t₁ t₂).entry (dBO t₁ t₂).kind).w) (εO t₁ t₂)).ior.red.out
            (tO, y) τ = some b →
        QN piO (NTuple (frO t₁ key) piO (fun z => t₁ + z) (fun s => rO s.st) rd) (tO, y)) :=
  law_O t₁ t₂ key W rd (tO, y) (promise_O t₁ t₂)

/-! ## The counts -/

theorem below_ofList (C : PQ.CK) : ∀ (lo : List (PQ.RD × List ℕ))
    (ε : Err (PQ.uL C (lo.map (·.1)))) (c : ENNReal), Err.Below ε c →
    Err.Below (errOfList (uLT C (lo.map mk)) (errList _ ε)) c
  | [], _, _, _ => trivial
  | _ :: lo, (_, ε), c, h => ⟨h.1, below_ofList C lo ε c h.2⟩

/-- **«Below» goes from a chain's rounds to a stretch that is like its written rounds.** -/
theorem below_like (dt : List RDT) (l : List WR) (h : List.Forall₂ Like dt l) (rds : List PQ.RD)
    (hr : rds = l.map WR.rd) (ε : Err (PQ.uL (ckP .two) rds)) (c : ENNReal)
    (hb : Err.Below ε c) : Err.Below (errOfList (uLT (ckP .two) dt) (errList _ ε)) c := by
  subst hr
  obtain ⟨lo, rfl, h2⟩ := like_lo dt l h
  revert ε
  rw [← h2]
  intro ε hb
  exact below_ofList (ckP .two) lo ε c hb

/-- **Every count of εO is at most 2⁻¹ ^ 128 of ITS OWN round's verifier messages, in the stretch's
shape.** From K12Condition at piO (Law/CondMembers.lean). -/
theorem small_O (t₁ t₂ : ℕ) : Err.Below (εO t₁ t₂) ((2 : ENNReal)⁻¹ ^ 128) :=
  below_like (dtO t₁ t₂) lO (like_O t₁ t₂) cO.rds cO_rds cO.errL _
    (Chain.errL_below cO _
      (H2K.Pub.k12Condition_piO_r.small aO restO w0O lO cO stages_O written_O cO_eq))

/-- **"BAT"'s own count, 768 · w, is at most 2⁻¹ ^ 128 of the verifier messages of THE STRETCH's first
round.** By batBelow_like (Law/BatValsPayAt.lean) and the kernel's o_price. -/
theorem bat_small_O (t₁ t₂ : ℕ) :
    RoundBelow 768 (OnBytes.Flat.toRD (dBO t₁ t₂)) ((2 : ENNReal)⁻¹ ^ 128) := by
  have h := H2K.Pin.batBelow_like piO rO 128 aO restO stages_O (dBO t₁ t₂) (dtO t₁ t₂)
    ⟨w0O, lO, written_O, .cons ⟨rfl, rfl, rfl, rfl, rfl⟩ (like_O t₁ t₂)⟩ H2K.Member.o_price
  rwa [H2K.Member.o_v0] at h

/-- εO's numbers are the chain's own. -/
theorem counts_O (t₁ t₂ : ℕ) : errList _ (εO t₁ t₂) = errList _ cO.errL :=
  errList_errOfList _ _ ((errList_length _ _).trans (len_cO t₁ t₂))

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.wants_dataOf
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_O
#print axioms VerifiableInference.Desc.K12.Coin.law_O
#print axioms VerifiableInference.Desc.K12.Coin.law_O_at
#print axioms VerifiableInference.Desc.K12.Coin.counts_O
#print axioms VerifiableInference.Desc.K12.Coin.below_like
#print axioms VerifiableInference.Desc.K12.Coin.small_O
#print axioms VerifiableInference.Desc.K12.Coin.bat_small_O
