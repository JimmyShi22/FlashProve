-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsLookups.lean: `BlockPlays` (E2E/OfflineRunsForm.lean) at the key file's two lookups: what these two
sub-protocols owe to "every run returns".

  `partPlays_sum`, `partPlays_quiet`   the masked sumcheck's part, lifted, and the part that sends nothing, lifted,
                         play at every state, where the declared rounds state what they say
  `two_of_shapeOk`       the library's test on a call's shape gives each variable two coefficients
  `stated_of_quiet`      a stage that sends nothing: its one round states nothing, in the form that the law asks
  `look_members_play`    every member of a lookup's side at owners plays at every state, under `RowStated`
  `look_block_plays`     the sub-protocol at a lookup's place in the key file's description plays, whatever the
                         state, the jobs, the coins: off the description's own test on its plan
  (At `keyProver K`'s first list: E2E/OfflineRunsKey.lean, `lookups_play`.)

It reads no book and no witness, and it spends nothing of `MidForm`. It says that no move errs and that every
message has the declared shape: nothing on what is sent. Nothing on any property.
-/
import E2E.OfflineRunsRows
import E2E.OfflineLookupFields
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysSum
import Johnson.Desc.ProofFile.Honest.Small.Plays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource lookupsOf)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)
open ProofFile.Honest.Small (statedOf plays_lift_quiet)
open ProofFile.Honest.SumLaw (StatedBy plays_lift_sumPart moves_length)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first)
open AtPublicFiles.KeyValues (faceAt)

section Parts
variable {V V' W W' X Y : Type}

/-- The masked sumcheck's part, lifted, plays at every state. -/
theorem partPlays_sum (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (hsg : ∀ x, set x (get x) = x) (name endName : String)
    (J : SumJob W' Y) (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) :
    PartPlays ((sumPart (V := V') name endName J).lift see wit get set) rs := by
  intro nm a v c ds back m hl
  have hl' : ds.length = (SumLaw.sumGs name endName J).length := by
    rw [hl, ← moves_length (V := V') name endName J]
    exact List.length_map _
  exact ⟨_, plays_lift_sumPart see wit get set hgs hsg name endName J c h2 nm a rs hr v ds hl' back m⟩

/-- The part that sends nothing in n rounds, lifted, plays at every state. -/
theorem partPlays_quiet (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (n : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (List.replicate n 0) rs) :
    PartPlays ((quietPart n : Part V' W' Y).lift see wit get set) rs := by
  intro nm a v c ds back m hl
  have hl' : ds.length = n := by
    rw [hl]
    show ((quietPart n : Part V' W' Y).moves.map _).length = n
    rw [List.length_map]
    simp [quietPart]
  exact ⟨_, plays_lift_quiet see wit get set hsg n c nm a rs hr v ds hl' back m⟩

end Parts

/-- The library's test on a call's shape gives each variable two coefficients at least. -/
theorem two_of_shapeOk {k : VerifiableInference.Desc.Part.MaskedSum.Call} (h : shapeOk k = true) :
    ∀ v ∈ k.vs, 2 ≤ v.d := by
  unfold shapeOk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro v hv
  have := h.1 v hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- One round that states nothing, in the form that the law on the quiet part asks. -/
theorem stated_of_quiet {rs : List (Fmt.DeclaredRound × List Oracle)} (h : statedOf rs = [([], [])]) :
    StatedBy (List.replicate 1 0) rs := by
  unfold statedOf at h
  cases rs with
  | nil =>
    rw [List.map_nil] at h
    cases h
  | cons r t =>
    cases t with
    | nil =>
      rw [List.map_cons, List.map_nil] at h
      have e := (List.cons.inj h).1
      exact ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2, trivial⟩
    | cons r' t' =>
      rw [List.map_cons, List.map_cons] at h
      have e := (List.cons.inj h).2
      cases e

section Members
variable {S Cl V W X Pb Wk : Type}

/-- **Every member of a lookup's side at owners plays at every state.** Conditional on hrow and
`RowStated`. -/
theorem look_members_play {σ : Side S Cl V W X Pb} (o : Owners) (R : Reads) (J : LookJobs Wk)
    (wit : W → Wk) (a : At)
    (hrow : σ.row = (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims a))
    (hSt : RowStated a.face σ) : ∀ u ∈ σ.members, PartPlays u.part u.rounds := by
  intro u hu
  obtain ⟨st, hst, hp, -⟩ := member_owned o R J wit a hrow u hu
  cases hc : st.call a.face with
  | some k =>
    obtain ⟨h1, h2, -⟩ := hSt.sums u hu st k hst hc
    have ep : partOfOwned (V := Unit) o R J a st u.number =
        sumPart (sumNameBy o st a.place u.number) (endNameBy o st a.place u.number)
          (jobOf R J a st k) := by
      unfold partOfOwned
      simp only [hc]
    rw [hp, ep]
    exact partPlays_sum (fun _ => ()) wit (fun _ => ()) (fun y _ => y) (fun _ _ => rfl) (fun _ => rfl)
      _ _ _ (two_of_shapeOk h1) _ h2
  | none =>
    have h1 := hSt.quiets u hu st hst hc
    have ep : partOfOwned (V := Unit) o R J a st u.number = ProofFile.Honest.quietPart 1 := by
      unfold partOfOwned
      simp only [hc]
      rfl
    rw [hp, ep]
    exact partPlays_quiet (fun _ => ()) wit (fun _ => ()) (fun y _ => y) (fun _ => rfl) 1 _
      (stated_of_quiet h1)

end Members

section Key
variable {V' W' Y' Pb Wk : Type}

/-- **The sub-protocol at a lookup's place in the key file's description plays**, whatever the state. -/
theorem look_block_plays {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hpl : (descriptionFromSource X N P).planOk = true) {i : Nat} (hi : i < (lookupsOf X.Y.k.oneTime).length)
    (o : Owners) (R : Reads) (J : LookJobs Wk) (wit : W' → Wk) (a : At)
    (hface : a.face = faceAt X i) {φ : Face V' W' Pb} {Bk : ProverCoinCounts}
    {hs : List (Placed V' W' Y')} {b : Block (descriptionFromSource X N P).S₁ (descriptionFromSource X N P).Cl}
    (hb : b ∈ (descriptionFromSource X N P).first.blocksInOrder) (hbp : b.place = ⟨1, some i, 2, .K3⟩)
    (hf : (hs.find? fun g => g.place == b.place) = some (proverSideOfLookupInChain o R J wit a))
    (Pre : Mid W' Y' → Prop) : BlockPlays φ Bk 0 hs b Pre := by
  obtain ⟨hok, es, e1, e2, e3⟩ := look_block X N P hpl hi hb hbp
  have hSt : RowStated a.face (⟨b, (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims (Pb := Pb) a),
      fun _ _ => none⟩ : Side (descriptionFromSource X N P).S₁ (descriptionFromSource X N P).Cl V' W' Y' Pb) :=
    rowStated_owned o R J wit a rfl es e1 e2 (by rw [hface]; exact e3) (by rw [hface]; exact hok)
  have hm := look_members_play o R J wit a rfl hSt
  have hrp := rowPartsPlay_of_members _ 0 _ hm
  have hlen : (proverSideOfLookupInChain (V₁ := V') (X₁ := Y') o R J wit a).parts.length =
      (lookSims (Pb := Pb) a).length := by
    have e := congrArg List.length (owned_seat_moves (V := V') (X := Y') o R J wit a)
    rw [List.length_map, List.length_map] at e
    rw [e, lookSims_length]
  have hrp' : RowPartsPlay (((proverSideOfLookupInChain (V₁ := V') (X₁ := Y') o R J wit a).parts.zip
      (lookSims (Pb := Pb) a)).map (·.1)) (b.rounds.zip b.oracles) := hrp
  rw [map_fst_zip_eq _ _ hlen] at hrp'
  exact blockPlays_of_parts hf hrp' Pre

end Key

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.partPlays_sum
#print axioms AtPublicFiles.OfflineRows.partPlays_quiet
#print axioms AtPublicFiles.OfflineRows.two_of_shapeOk
#print axioms AtPublicFiles.OfflineRows.stated_of_quiet
#print axioms AtPublicFiles.OfflineRows.look_members_play
#print axioms AtPublicFiles.OfflineRows.look_block_plays
