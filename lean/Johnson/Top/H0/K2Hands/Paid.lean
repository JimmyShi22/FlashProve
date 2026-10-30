-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/Paid.lean: the code switch: FOUR OF THE LAST JOIN's RECORDS OF
PREMISES (FrameOK, Names, NamesK, Slots) FOLLOW FROM ONE RECORD ON THE PROGRAM's OWN FRAME AND TEST,
at the two maps of names that are written out of the frame.

GenJoin.lean, KeptJoin.lean and KeptFormJoin.lean take FrameOK, Names, NamesK and Slots as premises,
with iJ and iQ as letters. Pays.lean pays their clauses on the frame and on public numbers one by
one, from switchFrame … = some W and switchTargetCheck … = true. DrawJoin.lean's names_at_maps and
namesK_at_maps pay the clauses on where entries lie, at the maps iJ and iQ of
Johnson/Top/H/SwitchMaps.lean. Here they are gathered.
  AtSwitch   THE ONE RECORD. Of the program: the frame is made; the target's test says yes AT THE
             SAME STATEMENT; g stands in it with the target's shape; the two old codes are no longer
             than 2^32; the number of kept rows is the sum of the members' rows; each kept member
             has a row, and its rows are just as long as the main row. Of the sending's list l: it
             begins with g's shape and goes on with the shapes of the messages that take the kept
             members. Of the typed stage: its two codes are the frame's. Of the slots: SlotsAll
             (Numbering.lean). Of the messages' numbers ids: g is the first of the sending, the
             message that takes kept member a is number 1 + a, and none of these is g.
  fit        Fit (Johnson/Top/H/SwitchMapsFit.lean), so that the two maps are there
  mapJ, mapQ  the two maps at that record
  paid_frame, paid_names, paid_namesK, paid_slots  FrameOK, Names, NamesK and Slots from AtSwitch,
             at these maps
  mapM_pairs, paid_claim  (mapM_pairs: a tool on lists, the same statement as
             K2Hears/SentRows.lean's mapM_zip) ClaimOK, from three clauses on the old claim (the
             main form's tensors have the main code's index bits; the two written-out vectors are no
             longer than the mask code's message) and one on the frame (two kept members have two
             old numbers)
LIMITS. AtSwitch is a PREMISE; nothing here shows that a run of the programs meets it. (Brought
further, not paid: AtYes.lean's atSwitch_of makes eight of its sixteen clauses at a yes of the
kind's decision.) The program asks the target's test at the statement IN FRONT OF the sending and
makes the frame at the statement behind the sending and the joins: that the test's yes carries over
is AtYes.lean's check_at_S3, by check_congr (Johnson/Top/H/SwitchPads.lean) with
K2Hears/BehindSame.lean's SameTables for the joins and K2Hears/SentKeeps.lean's SentOk for the
sending itself, UNDER KeptOld, and so under the premise KeptPos. TieN and Held are not paid here. No
soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.Pays
import Johnson.Top.H0.K2Hands.Numbering
import Johnson.Top.H0.K2Hands.ClaimJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

section
variable (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ) (anew : Array ℕ)
  (W : SwitchFrame) (l : List (OracleShape × ℕ)) (s : Sg) (K : Type) [Fintype K] [DecidableEq K]
  (mem row : K → ℕ) (pl : K → KeptPlace) (ids : ℕ → ℕ)

/-- **The one record.** -/
structure AtSwitch : Prop where
  frame : switchFrame S old T g anew = some W
  check : switchTargetCheck S old T = true
  gRec : ∃ x, S.oracles[g]? = some x ∧ x.shape = T.shape
  c32 : W.code.logN ≤ 32
  z32 : W.zk.logN ≤ 32
  keptRows : old.keptRows = (W.kept.map (·.rows)).sum
  rowsPos : ∀ (a : ℕ) (k : KeptPlace), W.kept[a]? = some k → 0 < k.rows
  ell : ∀ (a : ℕ) (k : KeptPlace), W.kept[a]? = some k →
    (S.codes.base.getD (S.oracles.getD k.old default).shape.code default).ell = W.code.ell
  first : ∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = T.shape
  next : ∀ i (hi : i < T.kept.size), ∃ h : 1 + i < l.length, (l.get ⟨1 + i, h⟩).1 = T.kept[i].shape
  codeC : s.C = codeOf W.code
  codeZ : s.Z = codeOf W.zk
  slots : SlotsAll K W mem row pl
  gIs : ∀ n : (sigOf S.codes l).Ent, ids (entAt S.codes l n).1 = W.g ↔ (entAt S.codes l n).1 = 0
  anewIs : ∀ (a : ℕ) (k : KeptPlace), W.kept[a]? = some k → ∀ n : (sigOf S.codes l).Ent,
    ids (entAt S.codes l n).1 = k.anew ↔ (entAt S.codes l n).1 = 1 + a
  notG : ∀ (a : ℕ) (k : KeptPlace), W.kept[a]? = some k → k.anew ≠ W.g

variable {S old T g anew W l s K mem row pl ids}

omit [Fintype K] [DecidableEq K] in
theorem AtSwitch.fit (A : AtSwitch S old T g anew W l s K mem row pl ids) :
    Fit S.codes l s W mem row pl := by
  obtain ⟨g0, hg⟩ := A.first
  exact fit_of_check S old T g anew W A.frame A.check l g0 hg A.next s A.codeC A.codeZ mem row pl
    A.slots.member A.slots.rowIn A.keptRows
    (fun k => le_of_eq (A.ell _ _ (A.slots.member k)).symm)

/-- The two maps of names at the record. -/
noncomputable def AtSwitch.mapJ (A : AtSwitch S old T g anew W l s K mem row pl ids) :
    (s.cKept K).J → (sigOf S.codes l).Ent := Johnson.Top.H.iJ s W mem row pl S.codes l A.fit.nameJ
noncomputable def AtSwitch.mapQ (A : AtSwitch S old T g anew W l s K mem row pl ids) :
    (s.cKept K).Q → (sigOf S.codes l).Ent := Johnson.Top.H.iQ s W mem row S.codes l A.fit.nameQ

omit [Fintype K] [DecidableEq K] in
theorem paid_frame (A : AtSwitch S old T g anew W l s K mem row pl ids) :
    FrameOK W W.parts.mainTailAt (W.parts.maskAt.getD 0 0) (W.parts.maskTailAt.getD 0 0)
      (W.parts.maskAt.getD 1 0) (W.parts.maskTailAt.getD 1 0) := by
  obtain ⟨x, hx, hxs⟩ := A.gRec
  exact frameOK_of_check S old T g anew W A.frame A.check x hx hxs A.c32 A.z32

theorem paid_names (A : AtSwitch S old T g anew W l s K mem row pl ids) :
    Names s K S.codes l A.mapJ A.mapQ W ids W.parts.mainTailAt (W.parts.maskAt.getD 0 0)
      (W.parts.maskTailAt.getD 0 0) (W.parts.maskAt.getD 1 0) (W.parts.maskTailAt.getD 1 0) := by
  obtain ⟨x, hx, hxs⟩ := A.gRec
  obtain ⟨g0, hg⟩ := A.first
  exact names_at_maps s W mem row pl S.codes l ids A.fit.nameJ A.fit.nameQ A.codeC A.codeZ A.gIs
    (mainIn_of_check S old T g anew W A.frame l g0 hg)
    (restIn_of_check S old T g anew W A.frame A.check l g0 hg x hx hxs)

theorem paid_namesK (A : AtSwitch S old T g anew W l s K mem row pl ids) :
    NamesK s K S.codes l A.mapJ A.mapQ W ids mem row pl
      (fun κ => W.parts.keptTailAt.getD (keptNo W (mem κ) (row κ)) 0) :=
  namesK_at_maps s W mem row pl S.codes l ids A.fit.nameJ A.fit.nameQ
    (fun κ => rowLt_of_frame S old T g anew W A.frame (mem κ) (pl κ) (A.slots.member κ) (row κ)
      (A.slots.rowIn κ))
    (fun κ => A.anewIs _ _ (A.slots.member κ))
    (fun κ => A.notG _ _ (A.slots.member κ))
    (fun κ => nodup_of_frame S old T g anew W A.frame (mem κ) (pl κ) (A.slots.member κ))
    (fun κ => padIn_of_check S old T g anew W A.frame (mem κ) (pl κ) (A.slots.member κ) A.check s
      A.codeC (A.ell _ _ (A.slots.member κ)) (A.rowsPos _ _ (A.slots.member κ)))
    (fun κ => keptIn_of_check S old T g anew W A.frame (mem κ) (pl κ) (A.slots.member κ) A.check s
      A.codeC (A.ell _ _ (A.slots.member κ)) l A.next)
    (fun κ => tailPieces_of_frame S old T g anew W A.frame (mem κ) (pl κ) (A.slots.member κ)
      A.keptRows (row κ) (A.slots.rowIn κ))
    (fun _ => places_inc S old T g anew W A.frame A.check _ _)

omit [Fintype K] [DecidableEq K] in
theorem paid_slots (A : AtSwitch S old T g anew W l s K mem row pl ids) (a : ℕ) (k : KeptPlace)
    (hk : W.kept[a]? = some k) : Slots s K S.codes l W ids mem row a k where
  anewIs := A.anewIs a k hk
  notG := A.notG a k hk
  nodup := nodup_of_frame S old T g anew W A.frame a k hk
  one := fun b hb => by
    obtain ⟨κ, hm, hr⟩ := A.slots.all a k b hk hb
    exact ⟨κ, ⟨hm, hr⟩, fun κ' hm' hr' => A.slots.two κ' κ (hm'.trans hm.symm) (hr'.trans hr.symm)⟩
  entry := entry_of_check S old T g anew W A.frame A.check s A.codeC a k hk (A.ell a k hk) l A.next
  pad := pad_of_check S old T g anew W A.frame A.check s A.codeC a k hk (A.ell a k hk)
    (A.rowsPos a k hk)

theorem mapM_pairs {α β : Type} (f : α → Option β) : ∀ (l : List α) (ks : List β),
    l.mapM f = some ks → ks.length = l.length ∧ ∀ p ∈ l.zip ks, f p.1 = some p.2
  | [], ks, h => by
    simp only [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun p hp => by simp at hp⟩
  | a :: l, ks, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        simp [ha, hl] at h
        subst h
        obtain ⟨e, hz⟩ := mapM_pairs f l bs hl
        refine ⟨by simp [e], fun p hp => ?_⟩
        rw [List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ha
        · exact hz p hp

omit [Fintype K] [DecidableEq K] in
theorem paid_claim (A : AtSwitch S old T g anew W l s K mem row pl ids)
    (mainVars : ∀ v ∈ old.c.tensors, v.vars = W.code.logEll)
    (d0 : (old.d.getD 0 #[]).size ≤ W.zk.ell) (d1 : (old.d.getD 1 #[]).size ≤ W.zk.ell)
    (twoOld : ∀ (a a' : ℕ) (k k' : KeptPlace), W.kept[a]? = some k → W.kept[a']? = some k' →
      k.old = k'.old → a = a')
    (ks : List KeptPlace) (hks : old.kept.toList.mapM (placeOf W) = some ks) :
    ClaimOK s K S.codes l W ids mem row pl old ks := by
  obtain ⟨hlen, hz⟩ := mapM_pairs (placeOf W) _ _ hks
  refine ⟨mainVars, d0, d1, fun p hp => ?_, hlen⟩
  have hf : W.kept.find? (·.old == p.1.oracle) = some p.2 := hz p hp
  have ho : p.2.old = p.1.oracle := by
    have := List.find?_some hf
    exact beq_iff_eq.1 this
  obtain ⟨a, hk⟩ := List.mem_iff_getElem?.1 (List.mem_of_find?_eq_some hf)
  refine ⟨ho, a, hk, paid_slots A a p.2 hk, fun κ => ⟨fun e => ?_, fun e => ?_⟩⟩
  · exact twoOld _ _ _ _ (A.slots.member κ) hk e
  · have h := A.slots.member κ
    rw [e, hk] at h
    rw [← Option.some.inj h]

end

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.paid_frame
#print axioms VerifiableInference.Desc.First.K2Hands.paid_names
#print axioms VerifiableInference.Desc.First.K2Hands.paid_namesK
#print axioms VerifiableInference.Desc.First.K2Hands.paid_slots
#print axioms VerifiableInference.Desc.First.K2Hands.paid_claim
