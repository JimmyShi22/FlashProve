-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/OfflineMembers.lean: the fields `exact` and `fresh` of `Good` at a lookup's row at owners
(`proverSideOfLookupInChain`, Honest/K3/RowOwned.lean), each part beside `lookSims`: the row that the key file's
prover lays.

  `member_owned`     a member of such a side is its stage's
  `owned_seat_moves`, `row_moves`, `rounds_owned`   the member's rounds are its stage's
  `rowStated_owned`  `RowStated` at such a side, from the block's entries
  `k3_exact_owned`   `ExactMember` at every member, at every On and bud, under `RowStated`
  `fresh_of_owns_none`   `FreshMember` at every member of a side whose parts nobody spends

Each is one part at a time, all else fixed before the coins: the spender's half alone. The statements
stand at jobs right or wrong: they say nothing on whether the job is the protocol's. That the
stretches a part spends are uniform and independent is taken, not shown: the owner's sentence is
`fresh` at the owner. No simulator is shown to be a simulator of the whole file. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K3.RowOwned
import Johnson.Desc.ProofFile.Honest.K3.RowQuietIs
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3RowStated
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact
import Johnson.Desc.ProofFile.Honest.Small.Quiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Oracle)
open VerifiableInference.Desc.K3 (entriesV entriesFit)
open ProofFile.Honest.Small (ExactMember FreshMember quietPart_exact_lift statedOf)
open ProofFile.Honest.SumLaw (StatedBy betaMarked statedBy_like statedBy_nums betaMarked_of_like
  exact_sumPart_field)

variable {S Cl V W X Pb Wk : Type}

/-- **A member of the side is its stage's.** Conditional on hrow. -/
theorem member_owned {σ : Side S Cl V W X Pb} (o : Owners) (R : Reads) (J : LookJobs Wk)
    (wit : W → Wk) (a : At)
    (hrow : σ.row = (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims a))
    (u : Member V W X Pb) (hu : u ∈ σ.members) :
    ∃ st, (stages a.face)[u.number]? = some st ∧
      u.part = (partOfOwned (V := Unit) o R J a st u.number).lift (fun _ => ()) wit (fun _ => ())
        (fun y _ => y) ∧
      u.sim = simOf a st u.number := by
  unfold Side.members at hu
  rw [hrow] at hu
  obtain ⟨i, x, hx, rfl⟩ := membersOf_spec _ 0 _ u hu
  unfold proverSideOfLookupInChain lookRowOwned lookSims at hx
  simp only [List.getElem?_zip_eq_some, List.getElem?_map, Option.map_eq_some_iff,
    List.getElem?_zipIdx, Nat.zero_add] at hx
  obtain ⟨⟨p, ⟨y, ⟨st, hst, rfl⟩, rfl⟩, h1⟩, ⟨y', ⟨st', hst', rfl⟩, h2⟩⟩ := hx
  obtain rfl : st = st' := Option.some.inj (hst.symm.trans hst')
  exact ⟨st, by simpa using hst, by simpa using h1.symm, by simpa using h2.symm⟩

/-- **The field `exact` at every member**, at every On and bud. Conditional on hrow and `RowStated`. -/
theorem k3_exact_owned (φ : Face V W Pb) {σ : Side S Cl V W X Pb} (o : Owners) (R : Reads)
    (J : LookJobs Wk) (wit : W → Wk) (a : At)
    (hrow : σ.row = (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims a))
    (hSt : RowStated a.face σ) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u := by
  intro u hu
  obtain ⟨st, hst, hp, hs⟩ := member_owned o R J wit a hrow u hu
  cases hc : st.call a.face with
  | some k =>
    obtain ⟨h1, h2, h3⟩ := hSt.sums u hu st k hst hc
    obtain ⟨j, rs, p, sm⟩ := u
    have hp' : p = (partOfOwned (V := Unit) o R J a st j).lift (fun _ => ()) wit (fun _ => ())
        (fun y _ => y) := hp
    have hs' : sm = simOf a st j := hs
    have es : simOf (Pb := Pb) a st j = sumSim ⟨a.place, j⟩ k := by
      unfold simOf
      simp only [hc]
    have ep : partOfOwned (V := Unit) o R J a st j =
        sumPart (sumNameBy o st a.place j) (endNameBy o st a.place j) (jobOf R J a st k) := by
      unfold partOfOwned
      simp only [hc]
    subst hp'
    rw [hs', es, ep]
    exact exact_sumPart_field φ σ chain firstTree On bud (fun _ => ()) wit (fun _ => ())
      (fun y _ => y) (fun _ _ => rfl) (fun _ => rfl) _ _ _ h1 rs h2 h3 j _
  | none =>
    have h1 := hSt.quiets u hu st hst hc
    obtain ⟨j, rs, p, sm⟩ := u
    have hp' : p = (partOfOwned (V := Unit) o R J a st j).lift (fun _ => ()) wit (fun _ => ())
        (fun y _ => y) := hp
    have hs' : sm = simOf a st j := hs
    have es : simOf (Pb := Pb) a st j = ProofFile.Honest.quietSim ⟨a.place, j⟩ 1 := by
      unfold simOf
      simp only [hc]
      rfl
    have ep : partOfOwned (V := Unit) o R J a st j = ProofFile.Honest.quietPart 1 := by
      unfold partOfOwned
      simp only [hc]
      rfl
    subst hp'
    rw [hs', es, ep]
    exact quietPart_exact_lift φ σ chain firstTree On bud j 1 rs _ (fun _ => ()) wit (fun _ => ())
      (fun y _ => y) h1

/-- **The field `fresh` at every member of a side whose parts nobody spends.** It carries nothing: it
holds of every such part by one term. -/
theorem fresh_of_owns_none (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List VerifiableInference.Desc.Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (hown : OwnsNone Bk σ) :
    ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u := fun u hu p sp ca m ds asks _ _ _ =>
  fresh_of_nil (Bk.spentBy ⟨σ.block.place, u.number⟩ p) (hown u hu p)
    (fun c => σ.shows φ u (c, sp, ca) m ds asks)
    (fun c => cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

/-- The numbers of moves of a seated row at owners are its stages' numbers of rounds. -/
theorem owned_seat_moves (o : Owners) (R : Reads) (J : LookJobs Wk) (wit : W → Wk) (a : At) :
    (proverSideOfLookupInChain (V₁ := V) (X₁ := X) o R J wit a).parts.map (·.moves.length) =
      (stages a.face).map (Stage.rounds a.face) := by
  show (((lookRowOwned (V := Unit) o R J a).map
      (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)).map (·.moves.length)) = _
  rw [List.map_map]
  have e : ((fun p : Part V W X => p.moves.length) ∘
      (Part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x)) =
      fun p : Part Unit Wk Unit => p.moves.length := by
    funext p
    exact List.length_map _
  rw [e, lookRowOwned_moves]
  exact lookRow_moves R J a

/-- The row's numbers of moves, with the simulators beside. -/
theorem row_moves (o : Owners) (R : Reads) (J : LookJobs Wk) (wit : W → Wk) (a : At) :
    ((proverSideOfLookupInChain (V₁ := V) (X₁ := X) o R J wit a).parts.zip (lookSims (Pb := Pb) a)).map
        (fun y => y.1.moves.length) = (stages a.face).map (Stage.rounds a.face) := by
  have hl : (proverSideOfLookupInChain (V₁ := V) (X₁ := X) o R J wit a).parts.length ≤
      (lookSims (Pb := Pb) a).length := by
    have e := congrArg List.length (owned_seat_moves (V := V) (X := X) o R J wit a)
    rw [List.length_map, List.length_map] at e
    rw [e, lookSims_length]
  have e : ((proverSideOfLookupInChain (V₁ := V) (X₁ := X) o R J wit a).parts.zip
      (lookSims (Pb := Pb) a)).map (fun y => y.1.moves.length) =
      (((proverSideOfLookupInChain (V₁ := V) (X₁ := X) o R J wit a).parts.zip
        (lookSims (Pb := Pb) a)).map Prod.fst).map (·.moves.length) := by
    rw [List.map_map]
    rfl
  rw [e, List.map_fst_zip hl]
  exact owned_seat_moves o R J wit a

/-- **A member's rounds are its stage's stretch of the sub-protocol's rounds.** -/
theorem rounds_owned {σ : Side S Cl V W X Pb} (o : Owners) (R : Reads) (J : LookJobs Wk)
    (wit : W → Wk) (a : At)
    (hrow : σ.row = (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims a))
    (u : Member V W X Pb) (hu : u ∈ σ.members) (st : Stage)
    (hst : (stages a.face)[u.number]? = some st) :
    u.rounds = ((σ.block.rounds.zip σ.block.oracles).drop (firstRound a.face st)).take
      (Stage.rounds a.face st) := by
  unfold Side.members at hu
  rw [hrow] at hu
  obtain ⟨i, x, hx, rfl⟩ := membersOf_spec _ 0 _ u hu
  have hi : (stages a.face)[i]? = some st := by simpa using hst
  have hm := row_moves (V := V) (X := X) (Pb := Pb) o R J wit a
  have e1 : ((((proverSideOfLookupInChain (V₁ := V) (X₁ := X) o R J wit a).parts.zip
      (lookSims (Pb := Pb) a)).take i).map fun y => y.1.moves.length).sum =
      firstRound a.face st := by
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hi
    rw [firstRound_getElem a.face i hlt, List.map_take, List.map_take, hm]
  have e2 : x.1.moves.length = Stage.rounds a.face st := by
    have h := congrArg (fun l => l[i]?) hm
    simp only [List.getElem?_map, hx, hi, Option.map_some] at h
    exact Option.some.inj h
  show ((σ.block.rounds.zip σ.block.oracles).drop _).take x.1.moves.length = _
  rw [e1, e2]

/-- A member's rounds are its stage's own entries, but for the work bits, declared bare. -/
theorem rounds_of_entries {σ : Side S Cl V W X Pb} (o : Owners) (R : Reads) (J : LookJobs Wk)
    (wit : W → Wk) (a : At)
    (hrow : σ.row = (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims a))
    (es : List Fmt.Entry) (hr : σ.block.rounds = es.map declOf)
    (ho : σ.block.oracles = es.map fun _ => []) (hfit : entriesFit a.face es = true)
    (hok : a.face.ok = true) (u : Member V W X Pb) (hu : u ∈ σ.members) (st : Stage)
    (hst : (stages a.face)[u.number]? = some st) :
    ∃ es' : List Fmt.Entry, u.rounds = es'.map (fun e => (declOf e, [])) ∧
      (es'.map fun e => { e with work := 0 }) = Stage.entries a.face st := by
  have hrs := rounds_owned o R J wit a hrow u hu st hst
  have h2 : 2 ≤ a.face.planes := by
    unfold VerifiableInference.Desc.K3.Face.ok at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1.1.1.1.2
  have he : (es.map fun e => { e with work := 0 }) = entriesV a.face := by
    unfold entriesFit at hfit
    exact of_decide_eq_true (by simpa using hfit)
  refine ⟨(es.drop (firstRound a.face st)).take (Stage.rounds a.face st), ?_, ?_⟩
  · rw [hrs, hr, ho, zip_bare, List.map_take, List.map_drop]
  · rw [List.map_take, List.map_drop, he]
    exact entries_at a.face h2 st (List.mem_of_getElem? hst)

/-- **`RowStated` at such a side.** Conditional on hrow and on: the sub-protocol declares just the
entries es, bare; it states an empty list of oracle messages for each; es are, but for the work bits,
the entries that the hearing goes by; the face passes its own test. -/
theorem rowStated_owned {σ : Side S Cl V W X Pb} (o : Owners) (R : Reads) (J : LookJobs Wk)
    (wit : W → Wk) (a : At)
    (hrow : σ.row = (proverSideOfLookupInChain o R J wit a).parts.zip (lookSims a))
    (es : List Fmt.Entry) (hr : σ.block.rounds = es.map declOf)
    (ho : σ.block.oracles = es.map fun _ => []) (hfit : entriesFit a.face es = true)
    (hok : a.face.ok = true) : RowStated a.face σ := by
  constructor
  · intro u hu st k hst hk
    obtain ⟨es', e1, e2⟩ := rounds_of_entries o R J wit a hrow es hr ho hfit hok u hu st hst
    have e3 : (es'.map fun e => { e with work := 0 }) =
        VerifiableInference.Desc.Part.MaskedSum.entries k := by
      rw [e2]
      unfold Stage.entries
      rw [hk]
    refine ⟨shapeOk_shape hok st k hk, statedBy_like k u.rounds ?_ ?_,
      betaMarked_of_like k u.rounds ?_⟩
    · rw [e1, ← e3, List.map_map, List.map_map]
      rfl
    · intro r hr'
      rw [e1] at hr'
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr'
      rfl
    · rw [e1, ← e3, List.map_map, List.map_map]
      rfl
  · intro u hu st hst hk
    obtain ⟨es', e1, e2⟩ := rounds_of_entries o R J wit a hrow es hr ho hfit hok u hu st hst
    have e3 : (es'.map fun e => { e with work := 0 }) =
        [VerifiableInference.Desc.K3.drawEntry st.name (st.draws a.face)] := by
      rw [e2]
      unfold Stage.entries
      rw [hk]
    have hS : StatedBy [0] u.rounds := by
      refine statedBy_nums [0] u.rounds ?_ ?_
      · have e4 : u.rounds.map (fun r => (r.1.entry.msg, r.1.entry.answers, r.1.entry.roots)) =
            (es'.map fun e => { e with work := 0 }).map fun e => (e.msg, e.answers, e.roots) := by
          rw [e1, List.map_map, List.map_map]
          rfl
        rw [e4, e3]
        rfl
      · intro r hr'
        rw [e1] at hr'
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr'
        rfl
    match hu' : u.rounds, hS with
    | [r], hS =>
      obtain ⟨a1, a2, _⟩ := hS
      show [(r.1.items.filter (· != .root), r.2)] = [([], [])]
      rw [a1, a2]
      rfl

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.member_owned
#print axioms AtPublicFiles.OfflineRows.k3_exact_owned
#print axioms AtPublicFiles.OfflineRows.fresh_of_owns_none
#print axioms AtPublicFiles.OfflineRows.owned_seat_moves
#print axioms AtPublicFiles.OfflineRows.rounds_owned
#print axioms AtPublicFiles.OfflineRows.rowStated_owned
