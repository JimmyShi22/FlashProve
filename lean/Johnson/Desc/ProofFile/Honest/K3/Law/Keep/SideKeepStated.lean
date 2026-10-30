-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/SideKeepStated.lean: the kind "lookup" (K3): the premises
`RowStated` (Honest/K3/Law/Good/K3ExactStated.lean) hold at a side that is seated over the row that
passes its tables on (`rowPairsKeep`, Honest/K3/Law/Keep/SideKeep.lean). Public facts on declared
rounds alone. Theorems; no definition.

Never to be retold as "the row that passes its tables on is simulated".

The road. `RowStated` reads of a member its number and its declared rounds alone. The row that
passes its tables on and the row that passes nothing on are cut alike: a part of either has as many
moves as its stage has rounds. So the sentence goes over from a side over the one to a side over the
other, where both have one sub-protocol.

A device of proof. The side from which it is carried is
`⟨σ'.block, rowPairs idleFill s, fallOf fs s.at_.place⟩`: the row at letters that hold nothing
(`idleFill`, Honest/K3/LotRow.lean): a side of no prover. It is seated wherever σ' is: one search
over one list at one place.

What is shown.
  `partKeep_moves`: conditional on `Keeps.Shaped`: a part of the row has as many moves as its stage
    has rounds. `lookSeatKeep_moves`: so for the seated row.
  `cut_alike`: conditional on `Keeps.Shaped`: `rowPairs` at whatever letters and `rowPairsKeep` are
    cut alike.
  `rowStated_cut`: `RowStated` goes over between two sides with one sub-protocol and rows cut alike.
  `rowStated_keep_of`: **the premises hold at the side.** The sister of `rowStated_of`
    (Honest/K3/Law/Good/K3RowStated.lean): its five premises, and `Keeps.Shaped`.
  `rowStated_keep`: **the same at a description's first chain, from `k3Fits`**: the sister of
    `rowStated_k3`, under its binders.

Kin. That the two rows' parts have the same counts of moves stands already in `seat_face`
(Honest/K3/Law/Keep/LotInstKeepLaw.lean [not in this library]), in the field moves of `SameFace`:
that file stands over more files; here it is had anew.

Limits. It shows the premise hSt of `k3_exact_kept` (Honest/K3/Law/Keep/ExactKept.lean); of that
sentence it shows nothing. `rowStated_keep` is conditional on `k3Fits`, a test with code on public
data of which the writers know no evaluation at the full size. No instance of its premises together
is exhibited. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.SideKeep
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.RowKeepFits
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3RowStated
import Johnson.Desc.ProofFile.Honest.AlikeFields.MembersCut
import Johnson.Desc.ProofFile.Honest.AlikeFields.ExactCarry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Chain FileDescription Oracle)
open VerifiableInference.Desc.K3 (entriesFit)
open ProofFile.Honest.AlikeFields (member_cut lastHandMoves_len)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {S Cl V W X X' Pb : Type}

/-! ## 1 The two rows are cut alike -/

/-- Conditional on hK: a part of the row has as many moves as its stage has rounds. -/
theorem partKeep_moves (Kp : Keeps) (a : At) (hK : Kp.Shaped a.face) (st : Stage) (i : Nat) :
    (partKeep (V := V) Kp a st i).moves.length = Stage.rounds a.face st := by
  have hKs := hK st
  unfold Stage.rounds
  cases hc : st.call a.face with
  | some k =>
    rw [hc] at hKs
    obtain ⟨Jk, hJ, rfl⟩ := Option.map_eq_some_iff.1 hKs
    have e : (keepPart (V := V) (sumName a.place i) (endName a.place i) Jk).moves.length =
        VerifiableInference.Desc.K3.roundsOf Jk.base.shape :=
      (Keep.keepPart_rounds _ _ Jk).trans
        ((Keep.sumPart_rounds (V := V) (sumName a.place i) (endName a.place i) Jk.base).symm.trans
          (sumPart_moves _ _ Jk.base))
    by_cases hb : st = .bits
    · subst hb
      rw [partKeep_bits Kp a i Jk hJ]
      exact (lastHandMoves_len _ _).trans e
    · rw [partKeep_some Kp a st i Jk hJ hb]
      exact e
  | none =>
    rw [hc] at hKs
    have hJ : Kp.job st = none := Option.map_eq_none_iff.1 hKs
    by_cases hα : st = .alpha
    · subst hα
      rw [partKeep_alpha Kp a i hJ]
      rfl
    · rw [partKeep_none Kp a st i hJ hα]
      rfl

/-- Conditional on hK: so for the seated row. -/
theorem lookSeatKeep_moves (Kp : Keeps) (wit : W → Ask) (get : X → RowOwn) (set : X → RowOwn → X)
    (a : At) (hK : Kp.Shaped a.face) :
    (proverSideOfLookupInChainKeepingTablesAtOneOwner (V₁ := V) Kp wit get set a).parts.map (·.moves.length) =
      (stages a.face).map (Stage.rounds a.face) := by
  have e : (lookRowKeep (V := Unit) Kp a).map (·.moves.length) =
      (stages a.face).map (Stage.rounds a.face) := by
    unfold lookRowKeep
    rw [List.map_map]
    have k : ((fun p : Part Unit Ask RowOwn => p.moves.length) ∘
        fun x : Stage × Nat => partKeep Kp a x.1 x.2) = fun x => Stage.rounds a.face x.1 := by
      funext x
      exact partKeep_moves Kp a hK x.1 x.2
    rw [k]
    exact map_zipIdx_fst _ _ 0
  rw [← e]
  simp [proverSideOfLookupInChainKeepingTablesAtOneOwner, Part.lift, Function.comp_def]

/-- Conditional on hK: the original pairs, at whatever letters, and the kept pairs are cut alike. -/
theorem cut_alike (A₀ : Fill W) (A : FillKeep W) (get : X' → RowOwn) (set : X' → RowOwn → X')
    (s : Site) (hK : (A.keeps s).Shaped s.at_.face) :
    (rowPairs (V := V) (X := X) (Pb := Pb) A₀ s).map (·.1.moves.length) =
      (rowPairsKeep (V := V) (Pb := Pb) A get set s).map (·.1.moves.length) := by
  have e1 : (rowPairs (V := V) (X := X) (Pb := Pb) A₀ s).map (·.1.moves.length) =
      ((rowPairs (V := V) (X := X) (Pb := Pb) A₀ s).map (·.1)).map (·.moves.length) := by
    rw [List.map_map]
    rfl
  have e2 : (rowPairsKeep (V := V) (Pb := Pb) A get set s).map (·.1.moves.length) =
      ((rowPairsKeep (V := V) (Pb := Pb) A get set s).map (·.1)).map (·.moves.length) := by
    rw [List.map_map]
    rfl
  rw [e1, e2, rowPairs_parts, rowPairsKeep_parts, proverSideOfLookupInChainAtOneOwner_moves, lookSeatKeep_moves _ _ _ _ _ hK]

/-! ## 2 The premises go over -/

/-- **`RowStated` goes over between two sides with one sub-protocol and rows cut alike.** -/
theorem rowStated_cut (f : LFace) (σ : Side S Cl V W X Pb) (σ' : Side S Cl V W X' Pb)
    (hb : σ'.block = σ.block)
    (hc : σ.row.map (·.1.moves.length) = σ'.row.map (·.1.moves.length)) :
    RowStated f σ → RowStated f σ' := by
  intro hS
  constructor
  · intro u' hu' st k hst hk
    obtain ⟨u, hu, e1, e2⟩ := member_cut σ σ' hb hc u' hu'
    rw [← e1] at hst
    rw [← e2]
    exact hS.sums u hu st k hst hk
  · intro u' hu' st hst hk
    obtain ⟨u, hu, e1, e2⟩ := member_cut σ σ' hb hc u' hu'
    rw [← e1] at hst
    rw [← e2]
    exact hS.quiets u hu st hst hk

/-- **The premises hold at the side.** Conditional on the side, hK, and on: the member found
declares just the entries es, bare; it states an empty list of oracle messages for each; es are, but
for the work bits, the entries that the hearing goes by; the face passes its own test. Carried from
a side of no prover: see the head. -/
theorem rowStated_keep_of (A : FillKeep W) (get : X → RowOwn) (set : X → RowOwn → X) (s : Site)
    (hK : (A.keeps s).Shaped s.at_.face) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ' : Side S Cl V W X Pb)
    (h : Side.seated bs s.at_.place (rowPairsKeep A get set s) fs = some σ')
    (es : List Fmt.Entry) (hr : σ'.block.rounds = es.map declOf)
    (ho : σ'.block.oracles = es.map fun _ => []) (hfit : entriesFit s.at_.face es = true)
    (hok : s.at_.face.ok = true) : RowStated s.at_.face σ' := by
  obtain ⟨hf, hrow, _⟩ := block_of_seated _ bs s.at_.place fs σ' h
  have hσ := seated_of_find (rowPairs (V := V) (X := Unit) (Pb := Pb) (idleFill : Fill W) s) bs
    s.at_.place fs σ'.block hf
  have hS := rowStated_of (idleFill : Fill W) s bs fs _ hσ es hr ho hfit hok
  refine rowStated_cut s.at_.face
    (⟨σ'.block, rowPairs (idleFill : Fill W) s, fallOf fs s.at_.place⟩ : Side S Cl V W Unit Pb) σ'
    rfl ?_ hS
  rw [hrow]
  exact cut_alike (idleFill : Fill W) A get set s hK

end

section
variable {V W X Pb : Type}

/-- **The same at a description's first chain, from "fits".** Conditional on the description's
return, the site, the lot's sub-protocol at the site's place, `k3Fits` at the chain's flat list, hK
and the side. -/
theorem rowStated_keep (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A₀ : SharedSeat)
    (B₀ : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A₀ B₀) (s : Site)
    (hs : s ∈ lookSites Z) (b : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : b.place = s.at_.place) (hF : k3Fits Z ch.blocksInOrder s = true) (A : FillKeep W)
    (get : X → RowOwn) (set : X → RowOwn → X) (hK : (A.keeps s).Shaped s.at_.face)
    (fs : List (Fall FS)) (σ' : Side FS ProofFile.Cl V W X Pb)
    (h : Side.seated ch.blocksInOrder s.at_.place (rowPairsKeep A get set s) fs = some σ') :
    RowStated s.at_.face σ' := by
  obtain ⟨hf, _, _⟩ := block_of_seated _ ch.blocksInOrder s.at_.place fs σ' h
  have hp : σ'.block.place = s.at_.place := by simpa using List.find?_some hf
  obtain ⟨m', hf', hk⟩ := plan_of_fits Z ch.blocksInOrder s hF
  obtain rfl : m' = σ'.block := Option.some.inj (hf'.symm.trans hf)
  have hm : σ'.block ∈ ch.blocksInOrder := List.mem_of_find?_eq_some hf
  have hmp : σ'.block.place = b.place := hp.trans hbs.symm
  obtain ⟨_, e1, _, e3, e4⟩ :=
    site_block o pol lay KL Fd Z Bs base ch A₀ B₀ O s hs b σ'.block hb hbs hm hmp hk
  obtain ⟨_, g1, g2, _⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A₀ B₀ O b hb σ'.block hm hmp
  exact rowStated_keep_of A get set s hK ch.blocksInOrder fs σ' h (s.p.entries.getD []) (g1.trans e3)
    (g2.trans e4) e1 (fits_gives Z ch.blocksInOrder s hF).2.2.1

end

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.partKeep_moves
#print axioms ProofFile.Honest.K3.Law.lookSeatKeep_moves
#print axioms ProofFile.Honest.K3.Law.cut_alike
#print axioms ProofFile.Honest.K3.Law.rowStated_cut
#print axioms ProofFile.Honest.K3.Law.rowStated_keep_of
#print axioms ProofFile.Honest.K3.Law.rowStated_keep
