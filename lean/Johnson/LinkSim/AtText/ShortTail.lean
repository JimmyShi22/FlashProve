-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/ShortTail.lean: a negative test of Spec.linkShiftIn's form, on the two
algorithms' output, as far as the first tree.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. A negative test: it takes one random value away from the coins and proves
that the simulation then fails. The value is the last entry of one row's tail; the row stands beside
the two folded rows in the prover's first tree. With that entry 0 in the prover's coins and in the
simulator's, what the two algorithms disclose differs, whatever the other coins are
(short_tail_fails). It holds under a premise that has not been proved for any concrete data, and its
proof reaches only the messages up to the first Merkle tree.
The row is the one beside the two folded rows in the first tree, which holds the packing of the
first fold's hiding polynomial. ShortPsi S C says that the coins C have 0 as the last entry of that
row's tail. That row's tail has Z.r entries, all of them coins (97 at the full size: fr_maskTail,
ShortTailAtFull.lean); Z is here the mask code S.P.Z, not the public files.

Main names (namespace OnBytes.LinkSim.AtText).
  short_tail_fails   Let parameters P, sizes S, t and verifier challenges D meet the public
                     premises on sizes (Sizes, SpecShift.lean) and PtsFull, and let X be any
                     data. Let the honest coins C and the simulator's coins C' both satisfy
                     ShortPsi. If the non-degeneracy premise holds at X and C (below), then
                     shownOf (linkAll P S t X C D) differs from shownOf (simAll P S t X C' D).
  short_not_upTo     so, if such coins C are 0 outside the places: the two algorithms do not
                     agree up to a shift of the coins that can be undone, on the coins that are
                     0 outside the places and satisfy ShortPsi (UpToShiftOn,
                     Johnson/LinkSim/UpToOn.lean).
  parts_of_shown     with no premise but Sizes: if the two algorithms disclose the same, then they
                     have the same front's rounds, the same first fold's rounds and the same
                     columns of the first tree at the positions opened.
Here t is the number of positions opened at the first stage (97 at the full size). The front is the
prover's first five rounds, before the first stage (lFront, Johnson/Prover/Link/LinkAll.lean).

Limits: the premise. The test is an implication. Its premise has two parts. PtsFull: the positions
at which the first tree is opened give as many distinct points as the mask code's tail is long.
Non-degeneracy: the last entry of the explicit shift of that row's tail is not 0 (shPsi P S t X X C
D (Z.r - 1) ≠ 0, Johnson/LinkSim/AtText/ShiftDefs.lean). shPsi takes two data, the one whose
contribution the shift compensates and the one of the run; here both are X. There is no concrete
data at which its non-degeneracy premise is proved to hold: in general form nothing can be
evaluated. Where the premise is never met, this file says nothing.

Limits: how far it reaches.
- It reaches one row of one tree, the first.
- The statement speaks of all that the two algorithms disclose. But its proof, and so its power,
  reach only the front, the first fold and the first tree.
- Of the rounds it reaches the first 5 + 1 + (1 + h + g): 15 of the 41 in dsFull at the full size
  (fr_rounds41, Johnson/Prover/Link/GroupsFull.lean; see Spec.lean, "41 and 42").
- Of the prover's own trees' groups it reaches the first. All later rounds and groups are taken as
  "there is a rest" and dropped (body_rs_cons, body_gs_cons).
- So it would not detect a tail that is an entry short at one of the later trees, a masking word
  struck at the base case, or a simulator that computes the base case's first element by the
  prover's own formula.

How it fits. Spec.linkShiftIn (Johnson/LinkSim/AtText/SpecShiftIn.lean) is proved, for the coins
that are 0 outside the places. homeExact is proved from it (Johnson/LinkSim/AtHome/Home.lean,
through home_upTo). Here its form, UpToShiftOn of the two algorithms, is tested against a smaller
set of coins. Where the premise is met, it fails on the short coins. At the first tree as many
positions are opened as that tail has entries (PtsFull), so every entry of the tail is determined.
ShortTailPts.lean and ShortTailAtFull.lean reduce PtsFull to a condition on the opened positions
alone; ShortTailToy.lean checks a part of the non-degeneracy premise in a small example.

How the proof goes, if both algorithms disclose the same. The answers to the link proof's own OOD
samples at the front are equal and the seed's factor is a unit, so the pads' difference is forced.
So the verifier's state is the same, and the members' messages differ by the explicit term dMem
(ShiftDefs.lean). The members are the two folded rows (Defs.lean). The fold's rounds are equal, so
the coefficients' difference is forced (foldRV_forces, FoldInjAt.lean). So the difference of that
row's message, which packs them, is forced. The first tree's columns are equal at the positions
opened. At as many distinct points as the tail has entries, this forces the differences of all the
tail's entries (tail_short_fails, resting on tail_unique, Johnson/LinkSim/TailUnique.lean): they
equal shPsi. Its last entry is not 0, while the two tails' last entries are 0.

Other names.
  smAt_single, ans_of_front, pad_forced, lMem_forced, lT_forced, muOf_first_add, W_forced,
  phi_forced         the steps of the proof above.
  lastSym_of_col     equal columns of the first tree give equal symbols of that row.
  body_rs_cons, body_gs_cons, bodyEnd_o_cons   the algorithm's rounds begin with the first
                     fold's rounds and its groups with the first tree's group, and there is a
                     rest.
  heads_of_set, split_rounds, group_cols   facts on lists alone.
  rounds_of_shown, cols_of_shown   the two halves of parts_of_shown.

Notes.
- On the premise. Argued on paper, not proved: the last entry of shPsi is the sum over j of entry j
  of that row's forced difference times the complete symmetric polynomial of degree j + 1 in the
  points. It is not 0 for generic data and challenges, and it is 0 at the data 0, as it must be.
  Stated and proved in Lean only in a small example with chosen values, for a part of what shPsi is
  made of, and not for the prover's algorithm: Johnson/LinkSim/AtText/ShortTailToy.lean, whose head
  says which part. The other half, PtsFull, is proved in general form from a premise on the opened
  positions alone (ShortTailPts.lean). At the full size it is proved, for every verifier message,
  from that condition at its challenges (ShortTailAtFull.lean).
- What holds without the premise is parts_of_shown. The public premises on sizes are a theorem at
  the full size (fr_sizes, Johnson/LinkSim/AtText/SeamAtFull3.lean). So shownOf does hold the
  front's rounds, the first fold's rounds and the first tree's opened columns. The lemmas on single
  parts are stated for all parameters, and so hold at the short coins too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.LinkShift
import Johnson.LinkSim.AtText.FoldInjAt
import Johnson.LinkSim.TailUnique

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open Johnson.Prover.Link

/-- The coins whose row beside the two folded rows has a tail with 0 as its last entry. -/
def ShortPsi (S : Sz) (C : LCoins) : Prop := C.ψN (S.P.Z.r - 1) = 0

open Classical in
/-- The opened positions give as many distinct points as the mask code's tail is long. -/
def PtsFull (P : P15) (S : Sz) (D : ℕ → Fmt.Drawn) : Prop :=
  ((q0 P D).map fun y => ptG S.P.Z.a (y % 2 ^ S.P.Z.a)).toFinset.card = S.P.Z.r

/-! ## The front -/

theorem smAt_single (S : Sz) (t : ℕ) (σ : (S.fam.om false).Z.D) (x : Bool → GE) (a : Bool) :
    smAt S t σ (mu0 S t fun b => Pi.single S.padJ (x b)) a = ((σ.2 : GEˣ) : GE) * x a := by
  rw [smAt_val]
  have h := val_add_single S.memb.Z σ 0 S.padJ (x a) ()
  rw [zero_add, val_zero] at h
  have hm : S.memb.Z.mat σ () S.padJ = ((σ.2 : GEˣ) : GE) := mat_std_pad S.memb σ
  rw [h, hm]
  exact zero_add _

section
variable {P : P15} {S : Sz} {t : ℕ} {X : LIn S} {C C' : LCoins} {D : ℕ → Fmt.Drawn}

theorem ans_of_front (h : lFront S t X C D = lFront S t (zeroIn X) C' D) (a : Bool) :
    smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) a =
      smAt S t (lSeed S D) (mu0 S t (lMem S (zeroIn X) C' D)) a := by
  unfold lFront at h
  have e := congrArg Fmt.RoundView.vals (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).1
  cases a
  · exact ofE_inj (Fmt.ItemValue.answer.inj (List.cons.inj e).1)
  · exact ofE_inj (Fmt.ItemValue.answer.inj (List.cons.inj (List.cons.inj e).2).1)

/-- The pads' difference is forced. -/
theorem pad_forced (hr : PadRoom S) (h : lFront S t X C D = lFront S t (zeroIn X) C' D) (a : Bool) :
    C'.pad a = C.pad a + shPad S t X D a := by
  have e := ans_of_front h a
  rw [lMem_split S X C D hr, lMem_zero S X C' D hr, smAt_add, smAt_single, smAt_single] at e
  have hb : (((lSeed S D).2 : GEˣ) : GE) ≠ 0 := Units.ne_zero _
  refine mul_left_cancel₀ hb ?_
  unfold shPad padShift fData
  rw [← e, mul_add, mul_inv_cancel_left₀ hb]
  exact add_comm _ _

theorem lMem_forced (hr : PadRoom S) (hp : ∀ a, C'.pad a = C.pad a + shPad S t X D a) :
    lMem S X C D = lMem S (zeroIn X) C' D + dMem S t X D := by
  have e : lMem S (zeroIn X) C' D =
      (fun a => Pi.single S.padJ (C.pad a) : Bool → S.MJ → GE) +
        (fun a => Pi.single S.padJ (shPad S t X D a) : Bool → S.MJ → GE) := by
    rw [lMem_zero S X C' D hr]
    funext a
    show (Pi.single S.padJ (C'.pad a) : S.MJ → GE) =
      Pi.single S.padJ (C.pad a) + Pi.single S.padJ (shPad S t X D a)
    rw [hp a, Pi.single_add]
  rw [e, lMem_split S X C D hr]
  unfold dMem fData
  abel

theorem lT_forced (h : lFront S t X C D = lFront S t (zeroIn X) C' D) :
    lT P S t X C D = lT P S t (zeroIn X) C' D := by
  unfold lT
  rw [h]
  rfl

theorem muOf_first_add (σ : Sg) (m m' : Bool → S.MJ → GE) (tN tN' : Bool → ℕ → ℕ → GE)
    (φ φ' ψ ψ' : ℕ → GE) :
    μOf σ (firstPS S (m + m') tN φ ψ) =
      μOf σ (firstPS S m tN' φ' ψ') + μOf σ (firstPS S m' 0 0 0) := by
  have e := firstPS_add S m m' tN' 0 φ' 0 ψ' 0
  have e1 : μOf σ (firstPS S (m + m') tN φ ψ) =
      μOf σ (firstPS S (m + m') (tN' + 0) (φ' + 0) (ψ' + 0)) := by
    funext x
    cases x <;> rfl
  rw [e1, e, muOf_add]

/-- The first fold's coefficients' difference is forced. -/
theorem W_forced (hm : lMem S X C D = lMem S (zeroIn X) C' D + dMem S t X D)
    (hT : lT P S t X C D = lT P S t (zeroIn X) C' D)
    (h : sRF C.body 0 ((p12Of P).nums.stages.headD default) 6 (lPS P S X C D)
        (rowOf (lT P S t X C D)) D =
      sRF C'.body 0 ((p12Of P).nums.stages.headD default) 6 (lPS P S (zeroIn X) C' D)
        (rowOf (lT P S t (zeroIn X) C' D)) D) :
    C'.body.W (sg0 P) 0 = C.body.W (sg0 P) 0 + shW0 P S t X X C D (sg0 P) := by
  unfold sRF at h
  rw [← hT] at h
  have e : μOf (sg0 P) (lPS P S X C D) =
      μOf (sg0 P) (lPS P S (zeroIn X) C' D) + μOf (sg0 P) (dTab0 S t X D) := by
    unfold lPS dTab0
    rw [hm]
    exact muOf_first_add _ _ _ _ _ _ _ _ _
  have h' : foldRV (sg0 P) (vecG (sg0 P) (rowOf (lT P S t X C D))) (μOf (sg0 P) (lPS P S X C D))
      (C.body.W (sg0 P) 0) (fun n => D (6 + n)) =
      foldRV (sg0 P) (vecG (sg0 P) (rowOf (lT P S t X C D)))
        (μOf (sg0 P) (lPS P S (zeroIn X) C' D)) (C'.body.W (sg0 P) 0) fun n => D (6 + n) := h
  rw [e] at h'
  rw [foldRV_forces _ _ _ _ _ _ _ h']
  unfold shW0
  rw [if_pos rfl]

theorem phi_forced (hW : C'.body.W (sg0 P) 0 = C.body.W (sg0 P) 0 + shW0 P S t X X C D (sg0 P)) :
    packedN (sg0 P) (C.body.W (sg0 P) 0) 0 =
      packedN (sg0 P) (C'.body.W (sg0 P) 0) 0 + dPhi P S t X X C D := by
  funext i
  show _ = packedN (sg0 P) (C'.body.W (sg0 P) 0) 0 i +
    -packedN (sg0 P) (shW0 P S t X X C D (sg0 P)) 0 i
  rw [hW, packedN_add]
  exact (add_neg_cancel_right _ _).symm

end

/-! ## The first tree's column -/

theorem lastSym_of_col (S : Sz) (mN mN' tN tN' : Bool → ℕ → ℕ → GE) (φ φ' ψ ψ' : ℕ → GE) (x : ℕ)
    (h : firstColW S mN tN φ ψ x = firstColW S mN' tN' φ' ψ' x) :
    symG S.P.Z (x % 2 ^ S.P.Z.a) φ ψ = symG S.P.Z (x % 2 ^ S.P.Z.a) φ' ψ' := by
  have g : ∀ (m u : Bool → ℕ → ℕ → GE) (f y : ℕ → GE),
      sym3 (firstColW S m u f y x) (3 * (S.P.R + S.P.R)) =
        ofE (symG S.P.Z (x % 2 ^ S.P.Z.a) f y) := by
    intro m u f y
    unfold firstColW
    rw [sym3_wordsOf _ _ (by rw [length_firstSyms]; omega)]
    unfold firstSyms
    rw [List.getD_append_right _ _ _ _ (by rw [length_wr]; omega), length_wr,
      List.getD_append_right _ _ _ _ (by rw [length_wr]; omega), length_wr]
    have e : S.P.R + S.P.R - S.P.R - S.P.R = 0 := by omega
    rw [e]
    rfl
  have e := congrArg (fun w => sym3 w (3 * (S.P.R + S.P.R))) h
  simp only [g] at e
  exact ofE_inj e

/-! ## From all that is disclosed to its parts -/

section
variable {P : P15} {S : Sz} {t : ℕ} {X : LIn S} {C C' : LCoins} {D : ℕ → Fmt.Drawn}

theorem body_rs_cons (p : P12) (K : BCoins) (next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (tt : T12) (PP : PS) (cc : ℕ → List UInt64) :
    ∃ T, (bodyAll p K (next :: rest) j cur l o tt PP cc D).rs =
      sRF K j cur o PP (rowOf tt) D ++ T := ⟨_, List.append_assoc _ _ _⟩

theorem body_gs_cons (p : P12) (K : BCoins) (next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (tt : T12) (PP : PS) (cc : ℕ → List UInt64) :
    ∃ G, (bodyAll p K (next :: rest) j cur l o tt PP cc D).gs =
      groupAt (sgOf cur).C.a (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss cc :: G :=
  ⟨_, rfl⟩

theorem bodyEnd_o_cons (p : P12) (K : BCoins) (next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (tt : T12) (PP : PS)
    (cc : ℕ → List UInt64) :
    o + ((sgOf cur).h + (sgOf cur).g) + 3 ≤
      (bodyEnd p K D (next :: rest) j cur l o tt PP cc).o := by
  show _ ≤ (bodyEnd p K D rest (j + 1) next _ (o + ((sgOf cur).h + (sgOf cur).g) + 3) _ _ _).o
  exact bodyEnd_o _ _ _ _ _ _ _ _ _ _ _

/-- Two lists that begin with parts of one length n, the second changed at an index from n on. -/
theorem heads_of_set {α : Type} (a a' b b' : List α) (n i : ℕ) (x : α) (ha : a.length = n)
    (ha' : a'.length = n) (hi : n ≤ i) (h : a ++ b = (a' ++ b').set i x) : a = a' := by
  have e := congrArg (List.take n) h
  rw [List.take_set_of_le hi, List.take_left' ha, List.take_left' ha'] at e
  exact e

theorem group_cols (a : ℕ) (poss : List ℕ) (c c' : ℕ → List UInt64)
    (h : groupAt a poss c = groupAt a poss c') :
    ∀ x ∈ Fmt.listOf (poss.map (· % 2 ^ a)), c x = c' x := by
  unfold groupAt at h
  exact fun x hx => (Prod.mk.inj (List.map_inj_left.1 h x hx)).2

/-- Lists alone: two lists of rounds that begin with a front, one round and a fold's rounds; the
second list changed at an index behind these. -/
theorem split_rounds {α : Type} (A A' Sm F F' BA BA' R1 R2 T1 T2 : List α) (r x : α) (m n i : ℕ)
    (hA : A = F ++ [r] ++ BA) (hBA : BA = R1 ++ T1) (hSm : Sm = A'.set i x)
    (hA' : A' = F' ++ [r] ++ BA') (hBA' : BA' = R2 ++ T2) (h : A = Sm) (hF : F.length = m)
    (hF' : F'.length = m) (h1 : R1.length = n) (h2 : R2.length = n) (hi : m + 1 + n ≤ i) :
    F = F' ∧ R1 = R2 := by
  subst hA hBA hSm hA' hBA'
  rw [← List.append_assoc, ← List.append_assoc] at h
  have e := heads_of_set (F ++ [r] ++ R1) (F' ++ [r] ++ R2) T1 T2 (m + 1 + n) i x
    (by rw [List.length_append, List.length_append, hF, h1]; rfl)
    (by rw [List.length_append, List.length_append, hF', h2]; rfl) hi h
  obtain ⟨a1, a2⟩ := List.append_inj e (by rw [List.length_append, List.length_append, hF, hF'])
  exact ⟨List.append_cancel_right a1, a2⟩

theorem rounds_of_shown {first next : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    (hst : (p12Of P).nums.stages = first :: next :: rest)
    (hrs : (linkAll P S t X C D).rs = (simAll P S t X C' D).rs) :
    lFront S t X C D = lFront S t (zeroIn X) C' D ∧
      sRF C.body 0 first 6 (lPS P S X C D) (rowOf (lT P S t X C D)) D =
        sRF C'.body 0 first 6 (lPS P S (zeroIn X) C' D) (rowOf (lT P S t (zeroIn X) C' D)) D := by
  obtain ⟨T1, e1⟩ := body_rs_cons (D := D) (p12Of P) C.body next rest 0 first
    ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D) (lPS P S X C D) (lCol P S X C D)
  obtain ⟨T2, e2⟩ := body_rs_cons (D := D) (p12Of P) C'.body next rest 0 first
    ((laidOf (p12Of P)).drop 1) 6 (lT P S t (zeroIn X) C' D) (lPS P S (zeroIn X) C' D)
    (lCol P S (zeroIn X) C' D)
  have hge := bodyEnd_o_cons (D := D) (p12Of P) C'.body next rest 0 first
    ((laidOf (p12Of P)).drop 1) 6 (lT P S t (zeroIn X) C' D) (lPS P S (zeroIn X) C' D)
    (lCol P S (zeroIn X) C' D)
  have L : ∀ (K : BCoins) (PP : PS) (row : GroupRow),
      (sRF K 0 first 6 PP row D).length = 1 + ((sgOf first).h + (sgOf first).g) := by
    intro K PP row
    unfold sRF
    exact length_foldRV _ _ _ _ _
  exact split_rounds _ _ _ _ _ _ _ _ _ T1 T2 _ _ 5 (1 + ((sgOf first).h + (sgOf first).g)) _
    (linkAll_rs_at hst X C) e1 (simAll_rs hst X C') (linkAll_rs_at hst (zeroIn X) C') e2 hrs rfl
    rfl (L _ _ _) (L _ _ _) (by omega)

theorem cols_of_shown {first next : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    (hst : (p12Of P).nums.stages = first :: next :: rest)
    (hgs : (linkAll P S t X C D).gs = (simAll P S t X C' D).gs) :
    ∀ x ∈ Fmt.listOf (q0 P D), lCol P S X C D x = lCol P S (zeroIn X) C' D x := by
  obtain ⟨G1, g1⟩ := body_gs_cons (D := D) (p12Of P) C.body next rest 0 first
    ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D) (lPS P S X C D) (lCol P S X C D)
  obtain ⟨G2, g2⟩ := body_gs_cons (D := D) (p12Of P) C'.body next rest 0 first
    ((laidOf (p12Of P)).drop 1) 6 (lT P S t (zeroIn X) C' D) (lPS P S (zeroIn X) C' D)
    (lCol P S (zeroIn X) C' D)
  rw [linkAll_gs_at hst X C, simAll_gs', linkAll_gs_at hst (zeroIn X) C', g1, g2] at hgs
  have hl : lStored P S (zeroIn X) D = lStored P S X D := rfl
  rw [hl] at hgs
  have hg := (List.cons.inj (List.append_cancel_left hgs)).1
  intro x hx
  refine group_cols _ _ _ _ hg x ?_
  unfold q0 openAt at hx
  rw [sg0_first hst] at hx
  exact hx

/-- Under Sizes, equal disclosed values give equal front rounds, equal first fold rounds and
equal columns of the first tree at the opened positions. -/
theorem parts_of_shown (hS : Sizes P S t D)
    (h : shownOf (linkAll P S t X C D) = shownOf (simAll P S t X C' D)) :
    lFront S t X C D = lFront S t (zeroIn X) C' D ∧
      sRF C.body 0 ((p12Of P).nums.stages.headD default) 6 (lPS P S X C D)
          (rowOf (lT P S t X C D)) D =
        sRF C'.body 0 ((p12Of P).nums.stages.headD default) 6 (lPS P S (zeroIn X) C' D)
          (rowOf (lT P S t (zeroIn X) C' D)) D ∧
      ∀ x ∈ Fmt.listOf (q0 P D), lCol P S X C D x = lCol P S (zeroIn X) C' D x := by
  obtain ⟨first, rest, hst, hF⟩ := hS.body
  have hne := rest_ne hS hst hF
  obtain ⟨next, rest', rfl⟩ : ∃ n r, rest = n :: r := by
    cases rest with
    | nil => exact absurd rfl hne
    | cons n r => exact ⟨n, r, rfl⟩
  have hh : (p12Of P).nums.stages.headD default = first := by
    rw [hst]
    rfl
  obtain ⟨a1, a2⟩ := rounds_of_shown hst (congrArg Prod.fst h)
  exact ⟨a1, by rw [hh]; exact a2, cols_of_shown hst (congrArg Prod.snd h)⟩

/-- With the last entry of that tail struck from both coins, and under Sizes, PtsFull and the
non-degeneracy premise, the two algorithms do not disclose the same. -/
theorem short_tail_fails (hS : Sizes P S t D) (hp : PtsFull P S D) (hC : ShortPsi S C)
    (hne : shPsi P S t X X C D (S.P.Z.r - 1) ≠ 0) (hC' : ShortPsi S C') :
    shownOf (linkAll P S t X C D) ≠ shownOf (simAll P S t X C' D) := by
  intro h
  obtain ⟨hFr, hRF, hcol⟩ := parts_of_shown hS h
  have hr := padRoom_of S hS.pad
  have hφ := phi_forced (W_forced (lMem_forced hr (pad_forced hr hFr)) (lT_forced (P := P) hFr) hRF)
  refine tail_short_fails _ (fun p => msgPart S.P.Z.r S.P.Z.l p (dPhi P S t X X C D)) S.P.Z.r hp hne
    (C'.ψN - C.ψN) ?_ ?_
  · show C'.ψN (S.P.Z.r - 1) - C.ψN (S.P.Z.r - 1) = 0
    rw [hC, hC']
    exact sub_zero _
  · intro p hpm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hpm)
    have hs := lastSym_of_col S _ _ _ _ _ _ _ _ y (hcol y ((Fmt.listOf_mem _ _).2 hy))
    rw [hφ, symG_eq, symG_eq] at hs
    unfold sym at hs
    rw [msgPart_add] at hs
    have e : ∑ q ∈ Finset.range S.P.Z.r, ptG S.P.Z.a (y % 2 ^ S.P.Z.a) ^ q * (C'.ψN - C.ψN) q =
        ∑ q ∈ Finset.range S.P.Z.r, ptG S.P.Z.a (y % 2 ^ S.P.Z.a) ^ q * C'.ψN q -
          ∑ q ∈ Finset.range S.P.Z.r, ptG S.P.Z.a (y % 2 ^ S.P.Z.a) ^ q * C.ψN q := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => mul_sub _ _ _
    show _ = msgPart S.P.Z.r S.P.Z.l (ptG S.P.Z.a (y % 2 ^ S.P.Z.a)) (dPhi P S t X X C D)
    rw [e]
    linear_combination -hs

/-- Under Sizes and PtsFull, if some coins C that are 0 outside the places and satisfy ShortPsi
meet the non-degeneracy premise, then on such coins the two algorithms do not agree up to a shift
that can be undone. -/
theorem short_not_upTo (hS : Sizes P S t D) (hp : PtsFull P S D) (hin : InPlaces P S C)
    (hC : ShortPsi S C) (hne : shPsi P S t X X C D (S.P.Z.r - 1) ≠ 0) :
    ¬ UpToShiftOn addC (fun B => InPlaces P S B ∧ ShortPsi S B)
      (fun B => InPlaces P S B ∧ ShortPsi S B) (fun B => shownOf (linkAll P S t X B D))
      (fun B => shownOf (simAll P S t X B D)) := by
  rintro ⟨s, _, hs⟩
  obtain ⟨hR, hf, -⟩ := hs C ⟨hin, hC⟩
  refine short_tail_fails hS hp hC hne (C' := addC C (s C)) ?_ hf
  show C.ψN (S.P.Z.r - 1) + (s C).ψN (S.P.Z.r - 1) = 0
  rw [hC, hR.2]
  exact add_zero _

end

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.parts_of_shown
#print axioms OnBytes.LinkSim.AtText.short_tail_fails
#print axioms OnBytes.LinkSim.AtText.short_not_upTo
