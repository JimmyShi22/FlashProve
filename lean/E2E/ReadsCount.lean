-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ReadsCount.lean: how many columns of a committed table the three files' verifiers read, at most,
from the rounds' data alone. Definitions, statements and proofs. General in the data: no size, no
public file, no honest prover occurs here.

The three verifiers. A whole file's verifier (`reductionOfWholeFile`, OnBytes/Maker/Whole.lean: the key file's
and the proof file's) has three chains (Fiat-Shamir hash chains) of rounds. A round's data list the
committed tables that are opened behind it (`RDT.stored`), each entry with the number `count` of
the round's sampled positions that are its part. The verifier reads the table at these positions,
each once. The verifier of a copy's file (`linkProtocolOfRoundData`, OnBytes/Flat/LinkSib.lean) reads two tables, the
first table and the copy, at the openings `xs`, each with its `count`.

What is shown.
  `storedSum ds`: the sum of all entries' counts over a chain's rounds. (The library's own summand:
    Johnson/Flat/Dec/FitAtWritten.lean.)
  `ext_len`: of what a chain's sampled positions ask for, at most `storedSum` are columns of the
    table, whatever was sampled.
  **`whole_card`**: at EVERY verifier randomness a whole file's verifier reads at most
    storedSum ds₁ + (storedSum ds₂ + storedSum ds₃) columns.
  `whole_two`: if the first and the third chain have the sum 0, the columns read are those that the
    second chain asks for.
  `rho₂_of_sh`: the second chain's verifier messages are a function of the shared verifier messages.
  **`whole_extShared`**, **`whole_readsAtMost`**: so, if the first and the third chain have the sum
    0, all requests of a batch read the same columns (the library's `ExtShared`), and ONE BATCH,
    whatever the number of its requests, reads at most storedSum ds₂ columns (`ReadsAtMost`).
  `sideXL_len`, `xSide_len`, `side_card`: for the rounds' data of the compiler's second form, the
    count by table that the library has for the first form (Run/PlanQXDoorProofs.lean; the proofs
    follow these, and the lemmas there that speak of openings alone are called).
  **`linkW_left`**, **`linkW_right`**: the verifier of a copy's file reads at most `cntOf false xs`
    columns of the first table and at most `cntOf true xs` of the copy. Asked: the numbers of the
    trees that its own rounds open are below 2^16 (else an own tree could be taken for a table).

Limits.
- The counts are of the set of positions that a protocol DECLARES as read (its field `extReads`).
  That a decision hangs on the table at these positions alone is the library's `IsLocal`
  (`wholeIOR_isLocal`, OnBytes/Maker/WholeLocal.lean; `linkW_local`, OnBytes/Flat/LinkSib.lean): it
  is not shown again here.
- Upper bounds. Nothing says that so many columns are read: equal positions are read once.
- A bound for one run of one verifier. How many runs a table serves is not treated here.
- At data without any stored entry all bounds are 0, and the statements hold for a verifier that
  reads no table at all. (At the written data the key file's and the proof file's verifiers read a
  column at every verifier randomness: E2E/ReadsNotEmpty.lean.) Whether a verifier that reads so few
  columns is sound is another matter.
- The proof-of-work bits of a round do not enter: the positions are read off a verifier message
  with these bits laid aside, so the bounds are the same with and without proof of work.
- Nothing on what is read of the prover's own oracles. Nothing on hiding.

BESIDE EVERY TELLING of the result on the index's committed tables, to which this file belongs
(E2E/WholeViewAtFiles.lean, E2E/TablesAtOwnObject.lean):
- placeholder provers: no message of the protocol is covered; it is not zero knowledge;
- before compilation: no hashing; each OOD seed is chosen before its table's coins are drawn, from
  nothing but what has been shown and coins of the environment's own: of a seed that hangs on
  anything hidden, another table's pads too, nothing is said;
- fresh uniform pads and encoding randomness for each table (as run: derived from the committer's
  secret seed); one OOD sample a table; one set of public files. One table's randomness is used
  under one set of public files alone. The same rows and pads under other public files would get
  another seed, and of two OOD samples on one table's pads this file says nothing.
- the budget is table by table, is kept by nobody, and has no slack: at one column more the
  interface's clause on the encoder fails (a theorem: some OOD seed, two matrices in range, at every
  set of that size; it states no size of the difference, only that the two laws differ; typed for
  the form with all OOD seeds alone); that the result itself fails there is typed by no environment;
- that the IOP's own tests on the public files pass is shown in the side library: at the library's
  two named sets of public files (AtFullSide/E2E/AtWrittenFiles.lean), and at the first set's files
  under every policy within four bounds (`theLive_zAt`, AtFullSide/Top/LiveAtPolicies.lean); no
  theorem ties any of these to a file on a disk.


-/
import OnBytes.Maker.ViewOrder
import OnBytes.Flat.LinkSib
import Blocks.Batch.KitHon
import Iop.BatchOne
import Fmt.Rules6Laws
import Run.PlanQXDoorProofs
import OnBytes.TypedOracleCompiler.Run.PlanQXLawsProofs

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Reads
open Iop
open OnBytes.Maker
open Compile.Joined (Chains)
open _root_.Run.PQ (CK View SgX XO keepS keepS_own sideA_len xsAt_side sum_split filterMap_len_le
  xPos_side cntOf xPos)
open TypedOracleCompiler.Run.PQ (RD wantedXL wantedX xWanted drawnSL)
open OnBytes.Flat (linkProtocolOfRoundData)

/-! ## 1. One chain -/

/-- The sum of the counts of all stored entries of a chain's rounds. -/
def storedSum (ds : List RDT) : ℕ := (ds.map fun d => (d.stored.map (·.count)).sum).sum

/-- A stored entry's part of a round's sampled positions has at most `count` members. -/
theorem partOf_len (s : _root_.Fmt.Stored) (poss : List ℕ) :
    (_root_.Fmt.partOf s poss).length ≤ s.count := by
  unfold _root_.Fmt.partOf
  exact List.length_take_le _ _

/-- What a round's sampled positions ask of the committed table of one stored entry. -/
def tableWants (a : ℕ) (poss : List ℕ) (s : _root_.Fmt.Stored) : List Want :=
  (_root_.Fmt.listOf ((_root_.Fmt.partOf s poss).map (· % 2 ^ a))).map fun x =>
    Want.table s.item x

theorem tableWants_len (a : ℕ) (poss : List ℕ) (s : _root_.Fmt.Stored) :
    (tableWants a poss s).length ≤ s.count := by
  unfold tableWants
  rw [List.length_map]
  refine le_trans (_root_.Fmt.listOf_len _) ?_
  rw [List.length_map]
  exact partOf_len s poss

/-- What a round's stored entries ask for: at most the sum of their counts. -/
theorem tables_len (a : ℕ) (poss : List ℕ) :
    ∀ ss : List _root_.Fmt.Stored,
      (ss.flatMap (tableWants a poss)).length ≤ (ss.map (·.count)).sum
  | [] => Nat.le_refl 0
  | s :: ss => by
      rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (tableWants_len a poss s) (tables_len a poss ss)

/-- The chain's wants, one round unfolded: the library's `wantsOf_cons`
(OnBytes/Maker/ViewOrder.lean) with `tableWants` for the stored entries' part. -/
theorem wantsOf_round (a : ℕ) (dep : ℕ → Option ℕ) (d : RDT) (ds : List RDT)
    (R : _root_.Fmt.Drawn) (Rs : List _root_.Fmt.Drawn) :
    wantsOf a dep (d :: ds) (R :: Rs) =
      d.stored.flatMap (tableWants a R.poss) ++ d.opens.flatMap (treeWants dep R.poss) ++
        wantsOf a dep ds Rs := wantsOf_cons a dep d ds R Rs

variable (D : WholeD)

/-- A leaf of a prover's tree is no column of the table. -/
theorem trees_map_none (j : ℕ) :
    ∀ l : List ℕ, (l.map fun x => Want.tree j x).filterMap (extPosOf D) = []
  | [] => rfl
  | _ :: l => trees_map_none j l

theorem treeWants_none (dep : ℕ → Option ℕ) (poss : List ℕ) (j : ℕ) :
    (treeWants dep poss j).filterMap (extPosOf D) = [] := by
  unfold treeWants
  cases dep j with
  | none => rfl
  | some b => exact trees_map_none D j _

theorem trees_none (dep : ℕ → Option ℕ) (poss : List ℕ) :
    ∀ js : List ℕ, (js.flatMap (treeWants dep poss)).filterMap (extPosOf D) = []
  | [] => rfl
  | j :: js => by
      rw [List.flatMap_cons, List.filterMap_append, treeWants_none D dep poss j,
        trees_none dep poss js, List.append_nil]

/-- **Of what a chain's sampled positions ask for, at most `storedSum` are columns of the table**,
whatever was sampled. -/
theorem ext_len (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (ds : List RDT) (Rs : List _root_.Fmt.Drawn),
      ((wantsOf a dep ds Rs).filterMap (extPosOf D)).length ≤ storedSum ds
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | d :: ds, R :: Rs => by
      rw [wantsOf_round, List.filterMap_append, List.filterMap_append, trees_none D dep R.poss,
        List.append_nil, List.length_append]
      exact Nat.add_le_add
        (le_trans (List.length_filterMap_le _ _) (tables_len a R.poss d.stored))
        (ext_len a dep ds Rs)

/-- A chain with the sum 0 asks for no column. -/
theorem ext_nil (a : ℕ) (dep : ℕ → Option ℕ) (ds : List RDT) (h : storedSum ds = 0)
    (Rs : List _root_.Fmt.Drawn) : (wantsOf a dep ds Rs).filterMap (extPosOf D) = [] :=
  List.eq_nil_of_length_eq_zero (Nat.le_zero.1 (h ▸ ext_len D a dep ds Rs))

/-! ## 2. A whole file -/

section Whole
variable (C : CK) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **At every verifier randomness a whole file's verifier reads at most as many columns as the
stored entries' counts add up to.** -/
theorem whole_card (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    ((reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ).card ≤
      storedSum D.ds₁ + (storedSum D.ds₂ + storedSum D.ds₃) := by
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.filterMap_append, List.filterMap_append, List.length_append, List.length_append]
  exact Nat.add_le_add (ext_len D D.a D.depth D.ds₁ _)
    (Nat.add_le_add (ext_len D D.a D.depth D.ds₂ _) (ext_len D D.a D.depth D.ds₃ _))

/-- If the first and the third chain have the sum 0, the columns read are those that the second
chain asks for. -/
theorem whole_two (h₁ : storedSum D.ds₁ = 0) (h₃ : storedSum D.ds₃ = 0)
    (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    (reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ =
      ((wantsOf D.a D.depth D.ds₂ (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ))).filterMap
        (extPosOf D)).toFinset := by
  show ((wantsOf D.a D.depth D.ds₁ (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)) ++
    (wantsOf D.a D.depth D.ds₂ (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) ++
      wantsOf D.a D.depth D.ds₃ (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)))).filterMap
        (extPosOf D)).toFinset = _
  rw [List.filterMap_append, List.filterMap_append, ext_nil D D.a D.depth D.ds₁ h₁,
    ext_nil D D.a D.depth D.ds₃ h₃, List.nil_append, List.append_nil]

end Whole

/-! ## 3. The second chain's verifier messages are shared -/

/-- Shared rounds in front: their verifier messages are among the shared ones. -/
theorem sh_front_eq :
    ∀ (s : Shape) {t : Shape} (B : RoundSplits t) {ρ ρ' : Rho (s ++ t)},
      Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) s) B) ρ =
        Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) s) B) ρ' →
      Rho.fst ρ = Rho.fst ρ'
  | [], _, _, _, _, _ => rfl
  | r :: s, _, B, (c, ρ), (c', ρ'), h => by
      have h1 : c = c' := congrArg Prod.fst h
      have h2 : Rho.fst ρ = Rho.fst ρ' := sh_front_eq s B (congrArg Prod.snd h)
      show ((c, Rho.fst ρ) : r.Chal × Rho s) = (c', Rho.fst ρ')
      rw [h1, h2]

/-- **The second chain's verifier messages are a function of the shared verifier messages.** -/
theorem rho₂_of_sh (G : Chains) {ρ ρ' : Rho G.sh} (h : Rho.sh G.ann ρ = Rho.sh G.ann ρ') :
    G.rho₂ ρ = G.rho₂ ρ' := by
  have h1 : Rho.sh (RoundSplits.app (RoundSplits.allLocal G.s₁) G.annJ) ρ.2 =
      Rho.sh (RoundSplits.app (RoundSplits.allLocal G.s₁) G.annJ) ρ'.2 := congrArg Prod.snd h
  have h2 : Rho.sh G.annJ (G.rhoJ ρ) = Rho.sh G.annJ (G.rhoJ ρ') :=
    Rho.sh_snd_eq (RoundSplits.allLocal G.s₁) G.annJ h1
  have h3 : Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) G.s₂) G.ann₃) (G.rhoJ ρ).2 =
      Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) G.s₂) G.ann₃) (G.rhoJ ρ').2 :=
    congrArg Prod.snd h2
  exact sh_front_eq G.s₂ G.ann₃ h3

section Batch
variable (C : CK) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- A whole file's protocol with its marks: the second chain's rounds are shared by a batch. -/
abbrev wholeBatch : BatchInteractiveOracleProof Xi (oneExternalString (2 ^ D.a) SgX) :=
  ⟨(reductionOfWholeFile C D tF tJ t3 silent run).toInteractiveOracleProof, (chainsOf C D tF tJ t3).ann⟩

/-- **All requests of a batch read the same columns**, if the first and the third chain have the
sum 0. -/
theorem whole_extShared (h₁ : storedSum D.ds₁ = 0) (h₃ : storedSum D.ds₃ = 0) :
    (wholeBatch D C tF tJ t3 silent run).ExtShared := by
  intro x x' ρ ρ' h
  show (reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ =
    (reductionOfWholeFile C D tF tJ t3 silent run).extReads ρ'
  rw [whole_two D C tF tJ t3 silent run h₁ h₃ ρ, whole_two D C tF tJ t3 silent run h₁ h₃ ρ',
    rho₂_of_sh (chainsOf C D tF tJ t3) h]

/-- **One batch, whatever the number N of its requests, reads at most q columns**, if the first and
the third chain have the sum 0 and the second at most q. -/
theorem whole_readsAtMost (h₁ : storedSum D.ds₁ = 0) (h₃ : storedSum D.ds₃ = 0) {q : ℕ}
    (h₂ : storedSum D.ds₂ ≤ q) (N : ℕ) : (wholeBatch D C tF tJ t3 silent run).ReadsAtMost N q :=
  BatchInteractiveOracleProof.readsAtMost_of_extShared _ (whole_extShared D C tF tJ t3 silent run h₁ h₃)
    (fun _ ρ => le_trans (whole_card D C tF tJ t3 silent run ρ) (by omega)) N

end Batch

/-! ## 4. The copy's file: the count by table, at the second form's rounds' data -/

theorem sideXL_len (a : ℕ) (all : List RD) (xs : List XO) (b : Bool) :
    ∀ (i : ℕ) (ds : List RD) (Ds : List _root_.Fmt.Drawn), (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
      ((wantedXL a all xs i ds Ds).filterMap (keepS b)).length ≤
        (((xs.filter fun o => o.which == b).filter fun o => decide (i ≤ o.round)).map
          (·.count)).sum
  | _, [], _, _ => by simp [wantedXL]
  | _, _ :: _, [], _ => by simp [wantedXL]
  | i, d :: ds, R :: Ds, h => by
      have ih := sideXL_len a all xs b (i + 1) ds Ds fun e he => h e (List.mem_cons_of_mem _ he)
      rw [wantedXL, List.filterMap_append, List.filterMap_append, List.length_append,
        List.length_append, sum_split i (xs.filter fun o => o.which == b), ← xsAt_side]
      refine le_trans
        (Nat.add_le_add
          (Nat.add_le_add (sideA_len a R b _)
            (Nat.le_of_eq
              (congrArg List.length
                (List.filterMap_eq_nil_iff.2 fun kx hkx => keepS_own b kx ?_))))
          ih) (by simp)
      obtain ⟨n, hn, hm⟩ := List.mem_flatMap.1 hkx
      split at hm
      · cases hm
      · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
        exact h d List.mem_cons_self n hn

/-- One table is asked for at no more positions than the counts of its own openings add up to. -/
theorem xSide_len (a : ℕ) (ds : List RD) (xs : List XO) (Ds : List _root_.Fmt.Drawn) (b : Bool)
    (h : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) :
    ((xWanted a ds xs Ds).filter fun wx => wx.1 == b).length ≤ cntOf b xs := by
  have h1 := sideXL_len a ds xs b 0 ds Ds h
  rw [List.filter_eq_self.2 (fun o _ => decide_eq_true (Nat.zero_le _))] at h1
  have e : ((xWanted a ds xs Ds).filter fun wx => wx.1 == b) =
      (wantedX a ds xs Ds).filterMap (keepS b) :=
    List.filter_filterMap
  rw [e]
  exact h1

theorem side_card (ds : List RD) (a : ℕ) (xs : List XO) (Ds : List _root_.Fmt.Drawn) (b : Bool)
    (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) :
    ((((xWanted a ds xs Ds).filterMap (xPos (2 ^ a))).toFinset).filter fun p =>
        (p.isRight == b) = true).card ≤ cntOf b xs := by
  rw [← List.toFinset_filter]
  refine le_trans (List.toFinset_card_le _) ?_
  rw [List.filter_filterMap]
  refine le_trans (filterMap_len_le _ (fun wx => wx.1 == b) (fun wx hs => ?_) _)
    (xSide_len a ds xs Ds b hown)
  cases hp : xPos (2 ^ a) wx with
  | none => rw [hp] at hs; cases hs
  | some p =>
      rw [hp] at hs
      have e := xPos_side _ wx p hp
      cases hb : (p.isRight == b) with
      | true =>
          show (wx.1 == b) = true
          rw [← e]
          exact hb
      | false => simp [Option.filter, hb] at hs

section Link
variable (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)
  (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
include hown

/-- **The verifier of a copy's file reads at most `cntOf false xs` columns of the first table.** -/
theorem linkW_left (x : X) (ρ : Rho (linkProtocolOfRoundData C ds a xs dec).shape) :
    (((linkProtocolOfRoundData C ds a xs dec).extReads x ρ).filter (fun p => p.isLeft)).card ≤ cntOf false xs := by
  have := side_card ds a xs (drawnSL C ds ρ.2) false hown
  refine le_trans
    (Nat.le_of_eq (congrArg Finset.card (Finset.filter_congr fun p _ => ?_))) this
  cases p <;> simp

/-- **It reads at most `cntOf true xs` columns of the copy.** -/
theorem linkW_right (x : X) (ρ : Rho (linkProtocolOfRoundData C ds a xs dec).shape) :
    (((linkProtocolOfRoundData C ds a xs dec).extReads x ρ).filter (fun p => p.isRight)).card ≤ cntOf true xs := by
  have := side_card ds a xs (drawnSL C ds ρ.2) true hown
  refine le_trans
    (Nat.le_of_eq (congrArg Finset.card (Finset.filter_congr fun p _ => ?_))) this
  cases p <;> simp

end Link

end AtPublicFiles.Reads

#print axioms AtPublicFiles.Reads.ext_len
#print axioms AtPublicFiles.Reads.whole_card
#print axioms AtPublicFiles.Reads.whole_two
#print axioms AtPublicFiles.Reads.rho₂_of_sh
#print axioms AtPublicFiles.Reads.whole_extShared
#print axioms AtPublicFiles.Reads.whole_readsAtMost
#print axioms AtPublicFiles.Reads.side_card
#print axioms AtPublicFiles.Reads.linkW_left
#print axioms AtPublicFiles.Reads.linkW_right
