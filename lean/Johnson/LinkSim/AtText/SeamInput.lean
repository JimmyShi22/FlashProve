-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamInput.lean: the data of the simulator's algorithm, made of what a
simulator of the link's protocol is given, and nothing else.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

A simulator of the link's protocol (linkProtocolOfRoundData, OnBytes/Flat/LinkSib.lean) is given the instance, the
verifier messages, and the symbols of the two stored tables (the link's input oracles; Defs.lean's
terms) at the positions that the verifier reads. The simulator's algorithm (simAll,
Johnson/LinkSim/AtText/Defs.lean) takes as input the same kind of data as the prover's
algorithm: both tables' rows, every stored column, the two keys. This file builds its data from the
instance and the symbols read, through a map keysOf from instances to keys.

What this file proves. Both statements hold for all parameters.
  Spec.simOfAns, simOfAns   suppose StoredTie (a public premise, below) holds at the challenges of
               the verifier message ρ, the honest data's keys are keysOf of the instance, and the
               honest data's stored columns are the columns of the input oracles. Then the
               simulator's algorithm gives the same output at the honest data and at inOf, taken at
               keysOf, the instance x and the symbols that the verifier reads (extAns x ρ of the
               input oracles). The proof is by simReads (Johnson/LinkSim/AtText/SimReads.lean).
  Spec.storedOfAns, storedOfAns   the step to simOfAns: under the first and third premises, the
               honest data's stored columns and those of inOf agree at every position that the
               algorithm opens (SameStored, Johnson/LinkSim/AtText/SpecShift.lean).
  inOf a keysOf x ans    the data built from what is given: rows 0; the stored columns colOfAns;
               the keys keysOf x. Besides the number a, its arguments are a map from instances to
               keys, the instance and the symbols read. None is an index, encoding randomness, a
               private input or the data that the prover's algorithm is given.

How it fits. inOf, with colOfAns and posOf, is part of the definition of the simulator: simLink
(Johnson/LinkSim/AtText/SpecExact.lean) runs simAll at inOf, and homeSim Z
(Johnson/LinkSim/AtHome/SpecHome.lean) is simLink at constants of the library and at Z's decision
function (Spec.lean, "the guard on what a simulator may read"). So these three definitions occur in
the statement of the main theorem, homeExactAt (Johnson/LinkSim/AtHome/HomeExactAll.lean). simOfAns
is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean), through
Johnson/LinkSim/AtText/Exact.lean.

The other names (namespace OnBytes.LinkSim.Seam; the lemmas that join the algorithms to the
protocol's types).
  colOfAns a ans b pos   the column in the symbol that ans holds at position pos of the first table
               (b false) or of the copy (b true); the empty list where ans holds none, or pos is out
               of range.
  StoredTie P a ds xs Ds   a public premise: each position at which the algorithm opens a stored
               table (at round 3) is below the tables' length, and is among what the protocol's
               challenges ask of that table. Here xs is the protocol's list of openings of the two
               stored tables: each names a round, a table, and which of that round's sampled
               positions it takes: from which place in the list on, and how many (XO).
  wantedXL_stored_mem, xWanted_mem   if an opening in xs is at a round that the rounds'
               description has, and that round's challenges are given, then the positions that it
               opens are among what the challenges ask of that table.
  storedOk, storedTie_of_ok   a Boolean test on public data, which Lean's kernel evaluates, and the
               lemma that it gives StoredTie at every list of challenges.

Limits. The honest data are a variable inW with two premises: its keys are keysOf of the instance,
and its stored column at a position in range is the column in the input oracles' symbol there. No
such map is defined here. One is homeIn (Johnson/LinkSim/AtHome/SpecHome.lean), and home_keys and
home_cols (Johnson/LinkSim/AtHome/HomeTies.lean) prove the two premises for it.

Notes. storedOk is evaluated in SeamAtFull2.lean, not here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SimReads
import Johnson.Prover.Link.LinkView
import OnBytes.Flat.LinkSib

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.LinkSim.AtText
open OnBytes.Flat (linkProtocolOfRoundData)
open _root_.Desc.K15 (P15 readsAtLink)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO SgX storedKey xsAt xPos)
open TypedOracleCompiler.Run.PQ (RD SOf drawnSL wantedX wantedXL xWanted)

/-- The place of position pos of the first table (b false) or of the copy (b true). -/
def posOf (a : ℕ) (b : Bool) (pos : ℕ) (h : pos < 2 ^ a) : (twoExternalStrings (2 ^ a) SgX).Pos :=
  if b then .inr ⟨pos, h⟩ else .inl ⟨pos, h⟩

/-- The column in the symbol that was read there; the empty list where none was read. -/
def colOfAns (a : ℕ) (ans : (twoExternalStrings (2 ^ a) SgX).Pos → Option SgX) (b : Bool) (pos : ℕ) :
    List UInt64 :=
  if h : pos < 2 ^ a then ((ans (posOf a b pos h)).map (·.2)).getD [] else []

/-- **The data of the simulator's algorithm**, made of the instance and the symbols read. -/
def inOf {S : Sz} {Xi : Type} (a : ℕ) (keysOf : Xi → TableKey × TableKey) (x : Xi)
    (ans : (twoExternalStrings (2 ^ a) SgX).Pos → Option SgX) : LIn S :=
  ⟨fun _ _ => 0, fun _ _ => 0, colOfAns a ans, keysOf x⟩

/-- A public premise: each position at which the algorithm opens a stored table is below the
tables' length and among what the challenges ask of that table. -/
def StoredTie (P : P15) (a : ℕ) (ds : List RD) (xs : List XO) (Ds : List Fmt.Drawn) : Prop :=
  ∀ st ∈ readsAtLink P.S,
    ∀ x ∈ Fmt.listOf ((Fmt.partOf st (drawsOf Ds 3).poss).map (· % 2 ^ st.sh.a)),
      x < 2 ^ a ∧ (st.item == 1, x) ∈ xWanted a ds xs Ds

/-- If an opening in xs is at a round that the rounds' description has, and that round's challenges
are given, its positions are among what the challenges ask of that table. -/
theorem wantedXL_stored_mem (a : ℕ) (all : List RD) (xs : List XO) (o : XO) (ho : o ∈ xs) :
    ∀ (i : ℕ) (ds : List RD) (Ds : List Fmt.Drawn) (D : Fmt.Drawn), i ≤ o.round →
    o.round - i < ds.length → Ds[o.round - i]? = some D → ∀ x ∈ o.list a D,
    (storedKey o.which, x) ∈ wantedXL a all xs i ds Ds
  | _, [], _, _, _, hl, _, _, _ => by simp at hl
  | _, _ :: _, [], _, _, _, hD, _, _ => by simp at hD
  | i, d :: ds, D0 :: Ds, D, hi, hl, hD, x, hx => by
      unfold wantedXL
      rcases Nat.eq_or_lt_of_le hi with e | hlt
      · refine List.mem_append_left _ (List.mem_append_left _ ?_)
        rw [← e, Nat.sub_self] at hD
        have e2 : D0 = D := by simpa using hD
        subst e2
        refine List.mem_flatMap.2 ⟨o, ?_, List.mem_map.2 ⟨x, hx, rfl⟩⟩
        unfold xsAt
        exact List.mem_filter.2 ⟨ho, by rw [e]; exact beq_self_eq_true _⟩
      · refine List.mem_append_right _ ?_
        have e3 : o.round - i = (o.round - (i + 1)) + 1 := by omega
        rw [e3] at hl hD
        exact wantedXL_stored_mem a all xs o ho (i + 1) ds Ds D hlt (by simpa using hl)
          (by simpa using hD) x hx

/-- An opening in xs at a round that the rounds' description has, with that round's challenges
given, puts its positions among what the challenges ask. -/
theorem xWanted_mem (a : ℕ) (ds : List RD) (xs : List XO) (Ds : List Fmt.Drawn) (o : XO)
    (ho : o ∈ xs) (D : Fmt.Drawn) (hl : o.round < ds.length) (hD : Ds[o.round]? = some D) (x : ℕ)
    (hx : x ∈ o.list a D) : (o.which, x) ∈ xWanted a ds xs Ds := by
  unfold xWanted wantedX
  refine List.mem_filterMap.2 ⟨(storedKey o.which, x),
    wantedXL_stored_mem a ds xs o ho 0 ds Ds D (Nat.zero_le _) hl hD x hx, ?_⟩
  cases o.which with
  | false => exact if_pos rfl
  | true =>
    show (if storedKey true = storedKey false then some (false, x)
      else if storedKey true = storedKey true then some (true, x) else none) = some (true, x)
    rw [if_neg (show ¬ storedKey true = storedKey false by decide), if_pos rfl]

/-- A Boolean test that Lean's kernel evaluates: there are more than three rounds; each stored table
that the algorithm opens has the tables' depth, and xs has an opening at round 3 of that table with
the same part of the challenges. -/
def storedOk (P : P15) (a : ℕ) (ds : List RD) (xs : List XO) : Bool :=
  decide (3 < ds.length) && (readsAtLink P.S).all fun st =>
    st.sh.a == a && xs.any fun o =>
      o.round == 3 && o.which == (st.item == 1) && o.from_ == st.lo && o.count == st.count

/-- The test gives the premise, at every list of challenges. -/
theorem storedTie_of_ok (P : P15) (a : ℕ) (ds : List RD) (xs : List XO) (Ds : List Fmt.Drawn)
    (h : storedOk P a ds xs = true) : StoredTie P a ds xs Ds := by
  unfold storedOk at h
  obtain ⟨h3, hall⟩ := Bool.and_eq_true_iff.1 h
  have h3' : 3 < ds.length := of_decide_eq_true h3
  intro st hst x hx
  obtain ⟨ha, hany⟩ := Bool.and_eq_true_iff.1 (List.all_eq_true.1 hall st hst)
  have ha' : st.sh.a = a := beq_iff_eq.1 ha
  obtain ⟨o, ho, hc⟩ := List.any_eq_true.1 hany
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  rw [ha'] at hx
  refine ⟨?_, ?_⟩
  · obtain ⟨y, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
    exact Nat.mod_lt _ (Nat.two_pow_pos a)
  · cases hD : Ds[3]? with
    | none =>
      have e : drawsOf Ds 3 = ⟨[], [], [], none⟩ := by
        show Ds.getD 3 _ = _
        rw [List.getD_eq_getElem?_getD, hD]
        rfl
      rw [e] at hx
      simp [Fmt.partOf, Fmt.listOf] at hx
    | some D =>
      have e : drawsOf Ds 3 = D := by
        show Ds.getD 3 _ = _
        rw [List.getD_eq_getElem?_getD, hD]
        rfl
      rw [e] at hx
      rw [← c2]
      refine xWanted_mem a ds xs Ds o ho D (by rw [c1]; exact h3') (by rw [c1]; exact hD) x ?_
      unfold XO.list XO.raw
      rw [c3, c4]
      exact hx

/-- Statement only; proved as storedOfAns below. The honest stored columns and those of inOf agree
where the algorithm opens them, under StoredTie and the premise that the honest columns are the
input oracles'. -/
def Spec.storedOfAns : Prop :=
  ∀ (K : CK) (ds : List RD) (a : ℕ) (xs : List XO) (Xi : Type) (dec : Xi → View → Bool) (P : P15)
    (S : Sz) (Wt : Type) (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str) (inW : Wt → Xi → LIn S)
    (keysOf : Xi → TableKey × TableKey) (w : Wt) (x : Xi)
    (ρ : Rho (_root_.Run.Twin.up (SOf K ds))),
    StoredTie P a ds xs (drawnSL K ds ρ.2) →
    (∀ b pos (h : pos < 2 ^ a),
      (inW w x).y b pos = ((twoExternalStrings (2 ^ a) SgX).rd (ext w) (posOf a b pos h)).2) →
    SameStored P (drawsOf (drawnSL K ds ρ.2)) (inW w x).y
      (inOf (S := S) a keysOf x ((linkProtocolOfRoundData K ds a xs dec).extAns x ρ (ext w))).y

/-- Proof of Spec.storedOfAns. -/
theorem storedOfAns : Spec.storedOfAns := by
  intro K ds a xs Xi dec P S Wt ext inW keysOf w x ρ hT hy st hst pos hpos
  obtain ⟨hlt, hmem⟩ := hT st hst pos hpos
  have hp : posOf a (st.item == 1) pos hlt ∈ (linkProtocolOfRoundData K ds a xs dec).extReads x ρ := by
    show posOf a (st.item == 1) pos hlt ∈
      ((xWanted a ds xs (drawnSL K ds ρ.2)).filterMap (xPos (2 ^ a))).toFinset
    refine List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hmem, ?_⟩)
    unfold xPos
    rw [dif_pos hlt]
    rfl
  rw [hy _ pos hlt]
  show _ = colOfAns a ((linkProtocolOfRoundData K ds a xs dec).extAns x ρ (ext w)) (st.item == 1) pos
  unfold colOfAns InteractiveOracleProof.extAns
  rw [dif_pos hlt, if_pos hp]
  rfl

/-- Statement only; proved as simOfAns below. So the simulator's algorithm gives the same output at
the honest data and at the data made of what is read. -/
def Spec.simOfAns : Prop :=
  ∀ (K : CK) (ds : List RD) (a : ℕ) (xs : List XO) (Xi : Type) (dec : Xi → View → Bool) (P : P15)
    (S : Sz) (t : ℕ) (Wt : Type) (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str) (inW : Wt → Xi → LIn S)
    (keysOf : Xi → TableKey × TableKey) (w : Wt) (x : Xi) (C : LCoins)
    (ρ : Rho (_root_.Run.Twin.up (SOf K ds))),
    StoredTie P a ds xs (drawnSL K ds ρ.2) → (inW w x).keys = keysOf x →
    (∀ b pos (h : pos < 2 ^ a),
      (inW w x).y b pos = ((twoExternalStrings (2 ^ a) SgX).rd (ext w) (posOf a b pos h)).2) →
    simAll P S t (inW w x) C (drawsOf (drawnSL K ds ρ.2)) =
      simAll P S t (inOf a keysOf x ((linkProtocolOfRoundData K ds a xs dec).extAns x ρ (ext w))) C
        (drawsOf (drawnSL K ds ρ.2))

/-- Proof of Spec.simOfAns. -/
theorem simOfAns : Spec.simOfAns :=
  fun K ds a xs Xi dec P S t Wt ext inW keysOf w x C ρ hT hk hy =>
    simReads P S t _ _ C _ hk (storedOfAns K ds a xs Xi dec P S Wt ext inW keysOf w x ρ hT hy)

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.storedTie_of_ok
#print axioms OnBytes.LinkSim.Seam.storedOfAns
#print axioms OnBytes.LinkSim.Seam.simOfAns
