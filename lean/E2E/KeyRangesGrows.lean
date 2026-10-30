-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesGrows.lean: THE SECOND CLAUSE OF `RangesOwes` (E2E/KeyRangesSeated.lean), "the rows
that the lookups left open on the ranges' group are true of the job's words", FOLLOWS FROM THE
THREAD's OWN OPEN SENTENCE, GIVEN ONE NAMED TIE ON THE LETTER L. Where the first chain's thread
`laid₁` stands at the border 15, the item `grows` is open, and the thread says it of L's witness:
every open row of the group and every sample row of message 1 holds at the witness
(Johnson/Desc/Key/KeyMeaning.lean). The law `allSay_of_grows`
(Johnson/Desc/ProofFile/Honest/K12/GrowsSays.lean) turns that into the clause where the witness's
message 1 reads as the words that the job makes. Definitions, statements and proofs.

  `grows_open15`   the item `grows` is among those open at the border 15: by evaluation of the
                 thread's closed table of rows
  **`grows_of_thr`**   so the thread says it, at L's witness at the challenges heard
  `WitIsJob`     THE TIE, A PREMISE's FORM: L's letter for sameness is "the two read as one
                 element"; and, on both tables of the statement's message 1, L's witness reads as
                 `wordsAt` of the job's plain rows: the multiplicities that the letter entry names,
                 and the masks that are the coins which the book carries to the test
  **`allSay_of_thr`**   in scope: the thread at 15 · `WitIsJob` ⟹ the clause
  **`owes_of_thr`**   with the first clause: `RangesOwes`

Limits. `WitIsJob` IS ASKED: it is shown of no L. It is a clause on how L's witness is made: it
names no row and no challenge of the lookups. THE CONTENT IS NOT PROVED HERE: IT IS TAKEN OFF THE
THREAD: that the thread stands at the border 15 with that sentence true is the debt of whoever pays
the first fifteen sub-protocols' rows of the thread, the lookups' among them. In scope; at the
written sizes. Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyRangesSeated
import Johnson.Desc.ProofFile.Honest.K12.GrowsSays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi FirstState Claim KItem valOf)
open VerifiableInference.Desc.Ground.Sh (stTidyB tidy_of stSh grpSh grp_get)
open OnBytes.Means (AllSay layoutOf tableSize)
open OnBytes.Slice (GF rdE begun runRows readE)
open AtPublicFiles.AtFiles (KeySourced rangesState)
open AtPublicFiles.AtFiles.Full (shape15_of_thr core15 loc15)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open Johnson.RunOne.KeyRows1 (meaning₁At plan₁ readers₁)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K12

variable {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles} {K : KeyPub}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
  (L : KeyFill (keyBook K) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins (keyBook K) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- The item `grows` is open at the border 15. -/
theorem grows_open15 : KItem.grows ∈ (laid₁ Xs N Pl L w₀ rc x hs tb).opened 15 := by
  show KItem.grows ∈ fwdOpen (VerifiableInference.Desc.Key.start₁ 2) rowsFirst 15
  decide

/-- **The thread says the item, at L's witness.** -/
theorem grows_of_thr {k : Coins (keyBook K)} {s : FirstState}
    {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E) :
    (meaning₁At (one₀ Xs) L.R).grows (m.st.input.x, s)
      ((laid₁ Xs N Pl L w₀ rc x hs tb).strs E)
      (L.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ []) []) :=
  hT.2.2.2.1 [] KItem.grows (grows_open15 Xs N Pl L w₀ rc x hs tb)

/-- **The tie between L's witness and the job.** s: the verifier's state. m: where the prover's run
stands. C: the coins that the term reads. -/
structure WitIsJob (k : Coins (keyBook K)) (s : FirstState) (m : Mid (Local W₀ Rc Xi Unit) X')
    (C : TestCoins) : Prop where
  same : L.R.same = fun a b => readE a = readE b
  words : ∀ G, s.d.st.groups[s.grp]? = some G → ∀ pt, ∀ i < tableSize s.d.st 1 pt,
    readE (valOf (plan₁ (one₀ Xs)) L.R
        (L.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ []) []) 1 pt i) =
      wordsAt (begun s.d.st s.grp G) (layoutOf s.d.st G)
        (plainOne (sentRanges Xs entry groups first) m.st.input (C.mem 0)
          ((rangesTestJob (X' := X') Xs N Pl entry groups first).first m.st.input (frontOf m) C)) 1 pt i

/-- **The clause, off the thread.** -/
theorem allSay_of_thr (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {k : Coins (keyBook K)} {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E) (C : TestCoins)
    (hW : WitIsJob (X' := X') Xs N Pl entry groups first L k s m C) (G : OnBytes.Group)
    (hG : (rangesState s).st.groups[(rangesState s).g]? = some G) :
    AllSay rdE (begun (rangesState s).st (rangesState s).g G)
      (runRows (rangesState s).st G).toList
      (wordsAt (begun (rangesState s).st (rangesState s).g G) (layoutOf (rangesState s).st G)
        (plainOne (sentRanges Xs entry groups first) m.st.input (C.mem 0)
          ((rangesTestJob (X' := X') Xs N Pl entry groups first).first m.st.input (frontOf m) C))) := by
  have hsh := shape15_of_thr hsrc scope (laid₁ Xs N Pl L w₀ rc x hs tb) rfl
    (fun _ _ _ _ _ hb => ⟨_, hb⟩) hT
  have hTidy : stTidyB s.d.st = true := (congrArg (·.2.tidy) hsh).trans loc15.2.2
  have hgrp : s.grp = 0 := (congrArg (·.2.grp) hsh).trans loc15.1
  have hG' : s.d.st.groups[s.grp]? = some G := hG
  have hmem : G.members.toList = [1] := by
    have e : (stSh s.d.st).groups[s.grp]? = some (grpSh G) := by rw [grp_get, hG']; rfl
    have e2 : stSh s.d.st = ProofFile.Honest.Sh.shKRFull.st :=
      congrArg (·.st) ((congrArg (·.1) hsh).trans core15)
    rw [e2, hgrp] at e
    have e3 : ProofFile.Honest.Sh.shKRFull.st.groups[0]?.map (·.members) = some [1] := by decide +kernel
    rw [e] at e3
    exact Option.some.inj e3
  exact allSay_of_grows (plan₁ (one₀ Xs)) L.R (readers₁ (one₀ Xs)) _ _ _ _ (m.st.input.x, s) _ _
    s.grp G 1 (by
      show (if s.grp == OnBytes.noId then none else some s.grp) = some s.grp
      rw [hgrp]
      rfl) hG' rfl hmem hW.same (tidy_of hTidy).inOrder (tidy_of hTidy).kinds _ _ (hW.words G hG')
    (grows_of_thr Xs N Pl L w₀ rc x hs tb hT)

/-- **`RangesOwes` from its first clause and the tie.** -/
theorem owes_of_thr (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {k : Coins (keyBook K)} {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E) (C : TestCoins)
    (hW : WitIsJob (X' := X') Xs N Pl entry groups first L k s m C)
    (hO : OldAt E ((rangesTestJob (X' := X') Xs N Pl entry groups first).trees₀ m.st.input (frontOf m)
      C.mem ((rangesTestJob (X' := X') Xs N Pl entry groups first).first m.st.input (frontOf m) C))
      (fun j => [Fmt.TreeSource.own 1].getD j (.own 0))) :
    RangesOwes (X' := X') Xs N Pl entry groups first s m E C :=
  ⟨hO, allSay_of_thr Xs N Pl entry groups first L w₀ rc x hs tb hsrc scope hT C hW⟩

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.grows_open15
#print axioms AtPublicFiles.KeyThread.grows_of_thr
#print axioms AtPublicFiles.KeyThread.allSay_of_thr
#print axioms AtPublicFiles.KeyThread.owes_of_thr
