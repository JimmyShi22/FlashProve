-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OwedOfKinds.lean: from the head AtHonest, the kinds and the threads' premises to Owed at the muted rows, and so to the online
clause of zero knowledge at the family onlineProversOfCommitter at the maker's prover.

1.  KindPays G κ, in Johnson/T3/KindPaysCore.lean: what is asked of one kind: at every list of parts of that kind, in each of the three chains,
    the fields fits, exact and fresh of Good, at the list's own On and bud, at the value of pre that the list's place gives.
2.  RowDebts: all that stays beside the head: the kinds, and each premise of the rule file_owed_hands_muteM by its name. Each list
    gives its On in one of two forms: OnFromS, or at the run's own front.
3.  owed_of_kinds: that rule, its premises hand₁, hand₂, hand₃ read off «∀ κ, KindPays G κ», six more given by the head.
4.  online_exact_of_honest, online_stops_of_honest, zeroKnowledgeOnServedRequests_of_honest: OnlineAtFiles.lean at that Owed, at the family
    onlineProversOfCommitter at the maker's prover A.H.
5.  sits, o₁₋₃, n₁₋₃ and OnFromS are asked at EVERY input, not at Rel's alone: so the threads must shut out stands whose trace is not the
    request's. With no rows every premise on rows is idle: what guards that is the tie to the protocol's prover and completeness at the
    same value.
6.  No value of any premise is given here: this file proves zero knowledge of nothing.
-/
import Johnson.T3.KindPaysCore
import Johnson.T3.OnlineAtFiles
import Johnson.T3.OwedMixed
import Johnson.Desc.ProofFile.Honest.AtHonest

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed
open ProofFile.Honest (Prover ProverCoinCounts Sides Owed relAt AtHonest OnlineProverWithDescription OnlineProverParts Good orderOf Thread Local Common
  Coins Mid Sits OwesS SaidNext Enters₁ Enters₂ DoorBehindS OnFromS depthAt ready BudDebts Ready preOf
  earlierOf RunOn₁ RunOn₂ RunOn₃ Committer ThreadsP ThreadDebts OnAtRun₁ OnAtRun₂ OnAtRun₃ silentAt runC)
open VerifiableInference.Desc (FileDescription KindName Chain)
open Compile.Lifetime (SimOf)

/-! ## 1 What is asked of one kind -/

section Kinds
variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F F' : FileDescription Xi} {Bk : ProverCoinCounts}

/-- The rows read at an equal description. -/
def sidesAt (h : F = F') (G : Sides F Bk W₀ Rc Ky Tr X₀ X) : Sides F' Bk W₀ Rc Ky Tr X₀ X := h ▸ G

theorem sidesAt_prover (h : F = F') (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) : (sidesAt h G).prover H = G.prover H := by
  subst h; rfl

theorem sidesAt_owns (h : F = F') (G : Sides F Bk W₀ Rc Ky Tr X₀ X) :
    (sidesAt h G).owns = G.owns := by
  subst h; rfl

theorem owed_sidesAt (h : F = F') {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} {Rel : W₀ → Rc → Xi → Prop} (o : Owed F Bk H G.mute Rel) :
    Owed F' Bk H (sidesAt h G).mute Rel := by
  subst h; exact o

end Kinds

/-! ## 2 Owed from the kinds -/

section Rule
variable {W₀ Rc Tr X₀ X : Type}

/-- **What stays beside the head**: the kinds, then each premise of the rule by its name. -/
structure RowDebts (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X)
    (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X) (Rel : W₀ → Rc → ProofFile.Inst → Prop)
    (T₁ : Local W₀ Rc ProofFile.Inst Tr → Thread A.B A.F.S₁ A.F.Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (T₂ : Common W₀ Rc OnBytes.TableKey → Thread A.B A.F.S₂ A.F.Cl Empty
      (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)
    (T₃ : Local W₀ Rc ProofFile.Inst Tr → Thread A.B A.F.S₃ A.F.Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (S₁ : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (S₂ : Common W₀ Rc OnBytes.TableKey → Nat → Coins A.B →
      Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    (S₃ : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    Prop where
  kinds : ∀ κ, KindPays G κ
  input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true
  hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ A.F.roundsDeclaredByBlocks.1 ++ A.F.roundsDeclaredByBlocks.2.1 ++ A.F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
    ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W
  hbud : BudDebts A.F A.B G
  sits : ∀ w w', Sits A.F (G.prover H) (T₁ w) (T₂ w') (T₃ w)
  o₁ : ∀ w, OwesS (T₁ w) (S₁ w)
  o₂ : ∀ w, OwesS (T₂ w) (S₂ w)
  o₃ : ∀ w, OwesS (T₃ w) (S₃ w)
  n₁ : ∀ w b, SaidNext (T₁ w) (S₁ w) b
  n₂ : ∀ w b, SaidNext (T₂ w) (S₂ w) b
  n₃ : ∀ w b, SaidNext (T₃ w) (S₃ w) b
  a₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
    Enters₁ A.F (G.prover H) (T₁ R.own) w₀ rc x k R
  a₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
    Enters₂ A.F (G.prover H) (T₂ R.common) w₀ rc x k R
  /-- the premise at the second chain's start, from the pair of thread and what is said -/
  d₃ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
    DoorBehindS A.F (G.prover H) (T₁ R.own) (T₂ R.common) (T₃ R.own) (S₁ R.own) (S₂ R.common)
      (S₃ R.own) x k R
  e₁ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
    S₁ R.own 0 k { R.start₁ (G.prover H) with opened := some [] }
  e₂ : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
    S₂ R.common 0 k { R.start₂ (G.prover H) with opened := some [] }
  on₁ : ∀ L ∈ G.first, (∀ w b blk, A.F.first.blocksInOrder[b]? = some blk → blk.place = L.place →
    OnFromS (T₁ w) (S₁ w) L b (depthAt A.F)) ∨ RunOn₁ A.F Rel H G L
  on₂ : ∀ L ∈ G.shared, (∀ w b blk, A.F.shared.blocksInOrder[b]? = some blk → blk.place = L.place →
    OnFromS (T₂ w) (S₂ w) L b (depthAt A.F)) ∨ RunOn₂ A.F Rel H G L
  on₃ : ∀ L ∈ G.second, (∀ w b blk, A.F.second.blocksInOrder[b]? = some blk → blk.place = L.place →
    OnFromS (T₃ w) (S₃ w) L b (depthAt A.F)) ∨ RunOn₃ A.F Rel H G L

/-- **What stays beside the head, in the form of one run's invariants.** threads: at every input of Rel and every return of ready, a value of
ThreadsP at this prover, what ThreadsC.thru and rows_of_thru end in through ThreadsC.toP, and each list's On
at that value, list by list: OnAtRun₁₋₃ hand it what a run holds before the part. -/
structure RowDebtsP (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X)
    (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X) (Rel : W₀ → Rc → ProofFile.Inst → Prop) : Prop where
  kinds : ∀ κ, KindPays G κ
  input : ∀ w₀ rc x, Rel w₀ rc x → H.inRange w₀ = true ∧ (H.trace w₀ x).isSome = true
  hst : ∀ w₀ rc x, Rel w₀ rc x → ∀ d ∈ A.F.roundsDeclaredByBlocks.1 ++ A.F.roundsDeclaredByBlocks.2.1 ++ A.F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored,
    ∀ y, y < 2 ^ t.sh.a → ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W
  hbud : BudDebts A.F A.B G
  threads : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready A.F A.B (G.prover H) w₀ rc x k = .ok R →
    ∃ T : ThreadsP A.F A.B (G.prover H) w₀ rc x k R, ∀ ρ r, ρ.due A.F = true →
      silentAt A.F (G.prover H) w₀ rc x ρ = none →
      runC A.F A.B (G.prover H) w₀ rc x k ρ = .ok r →
      (∀ L ∈ G.first, OnAtRun₁ (G := G) (H := H) T ρ r L) ∧
      (∀ L ∈ G.shared, OnAtRun₂ (G := G) (H := H) T ρ r L) ∧
      ∀ L ∈ G.second, OnAtRun₃ (G := G) (H := H) T ρ r L

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} {P : OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X}
  {more : List (String × Bool)} {Rel : W₀ → Rc → ProofFile.Inst → Prop}
  {T₁ : Local W₀ Rc ProofFile.Inst Tr → Thread A.B A.F.S₁ A.F.Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {T₂ : Common W₀ Rc OnBytes.TableKey → Thread A.B A.F.S₂ A.F.Cl Empty
      (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey}
  {T₃ : Local W₀ Rc ProofFile.Inst Tr → Thread A.B A.F.S₃ A.F.Cl (Local W₀ Rc ProofFile.Inst Tr)
      (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {S₁ : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
  {S₂ : Common W₀ Rc OnBytes.TableKey → Nat → Coins A.B →
      Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop}
  {S₃ : Local W₀ Rc ProofFile.Inst Tr → Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}

/-- ready returns at the committer's prover, at every input of Rel, from the head's one return. -/
theorem ready_of_head (hd : AtHonest o Z D r Zp Np cF x P A G more) {Sd Xc : Type}
    (Cm : Committer W₀ Rc Sd Xc ProofFile.Inst OnBytes.TableKey) (item : Nat)
    (input : ∀ w₀ rc x, Rel w₀ rc x → (Cm.proverAt item A.H).inRange w₀ = true ∧
      ((Cm.proverAt item A.H).trace w₀ x).isSome = true) :
    ∀ w₀ rc x, Rel w₀ rc x → ∀ k, ∃ R, ready A.F A.B (G.prover (Cm.proverAt item A.H)) w₀ rc x k = .ok R := by
  obtain ⟨w₁, rc₁, ξ₁, k₁, R₁, h₁⟩ := hd.one
  have h₂ : ready A.F A.B (G.prover A.H) w₁ rc₁ ξ₁ k₁ = .ok R₁ := by rw [hd.ring]; exact h₁
  obtain ⟨R₂, hone⟩ := ProofFile.Honest.ready_of_same (H := G.prover A.H)
    (H' := G.prover (Cm.proverAt item A.H)) rfl rfl rfl rfl rfl rfl h₂
  exact fun w₀ rc x hrel k => ProofFile.Honest.ready_any hone (input w₀ rc x hrel).1 (input w₀ rc x hrel).2 k

/-- **Owed at the term's rows from the kinds**, at the maker's prover with a committer's key and columns, as the family onlineProversOfCommitter lays it.
plan, book, seats, seal, rooted and one ready run come from the head: rooted, and whether ready returns, do not read the key or the
columns. -/
theorem owed_of_kindsP (hd : AtHonest o Z D r Zp Np cF x P A G more) {Sd Xc : Type}
    (Cm : Committer W₀ Rc Sd Xc ProofFile.Inst OnBytes.TableKey) (item : Nat)
    (debts : RowDebtsP A G (Cm.proverAt item A.H) Rel) :
    Owed A.F A.B (Cm.proverAt item A.H) G.mute Rel :=
  have hand₁ := fun L hL σ hσ => (debts.kinds L.place.kind).1 L hL rfl σ hσ
  have hand₂ := fun L hL σ hσ => (debts.kinds L.place.kind).2.1 L hL rfl σ hσ
  have hand₃ := fun L hL σ hσ => (debts.kinds L.place.kind).2.2 L hL rfl σ hσ
  ProofFile.Honest.owed_mute_of_threads_at_run hd.plan hd.book hd.seats hd.seal hd.rooted hand₁ hand₂ hand₃
    debts.input debts.hst (ready_of_head hd Cm item debts.input)
    (fun w₀ rc x h k R hR => Classical.choose (debts.threads w₀ rc x h k R hR))
    (fun _ _ _ _ _ _ hR => ProofFile.Honest.partsStand_of_hand hd.plan hd.book hd.seats hand₁ hand₂ hand₃ hR)
    debts.hbud
    (fun w₀ rc x h k R hR => Classical.choose_spec (debts.threads w₀ rc x h k R hR))

/-- **The form with Thread values is a case of it**: Thread values with their debts give the invariants, and an On from the thread is carried to the run. -/
theorem RowDebts.toP (hd : AtHonest o Z D r Zp Np cF x P A G more) {Sd Xc : Type}
    (Cm : Committer W₀ Rc Sd Xc ProofFile.Inst OnBytes.TableKey) (item : Nat)
    (debts : RowDebts A G (Cm.proverAt item A.H) Rel T₁ T₂ T₃ S₁ S₂ S₃) :
    RowDebtsP A G (Cm.proverAt item A.H) Rel :=
  have d : ThreadDebts A.F A.B (G.prover (Cm.proverAt item A.H)) Rel T₁ T₂ T₃ S₁ S₂ S₃ :=
    ⟨hd.plan, debts.sits, debts.o₁, debts.o₂, debts.o₃, debts.n₁, debts.n₂, debts.n₃, debts.a₁,
      debts.a₂, debts.d₃, debts.e₁, debts.e₂⟩
  { kinds := debts.kinds
    input := debts.input
    hst := debts.hst
    hbud := debts.hbud
    threads := fun w₀ rc x h k R hR => ⟨d.threads w₀ rc x h k R hR, fun ρ r hρ hs hr =>
      ⟨fun L hL => (debts.on₁ L hL).elim
          (fun hF => ProofFile.Honest.onAtRun₁_of_fromS d h hR hρ r hF)
          (fun hN => ProofFile.Honest.onAtRun₁_of_runOn h _ hρ hs hr hN),
        fun L hL => (debts.on₂ L hL).elim
          (fun hF => ProofFile.Honest.onAtRun₂_of_fromS d h hR hρ r hF)
          (fun hN => ProofFile.Honest.onAtRun₂_of_runOn h _ hρ hs hr hN),
        fun L hL => (debts.on₃ L hL).elim
          (fun hF => ProofFile.Honest.onAtRun₃_of_fromS d h hR hρ r hF)
          (fun hN => ProofFile.Honest.onAtRun₃_of_runOn h _ hρ hs hr hN)⟩⟩ }

/-- **Owed from the form with Thread values.** -/
theorem owed_of_kinds (hd : AtHonest o Z D r Zp Np cF x P A G more) {Sd Xc : Type}
    (Cm : Committer W₀ Rc Sd Xc ProofFile.Inst OnBytes.TableKey) (item : Nat)
    (debts : RowDebts A G (Cm.proverAt item A.H) Rel T₁ T₂ T₃ S₁ S₂ S₃) :
    Owed A.F A.B (Cm.proverAt item A.H) G.mute Rel :=
  owed_of_kindsP hd Cm item (RowDebts.toP hd Cm item debts)

end Rule

/-! ## 3 The online clause of zero knowledge at the maker's prover -/

section AtFiles
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) owedOfKindsInstance1 : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) owedOfKindsInstance2 {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} {D : WholeD} {r : LPFD.Full.RunPF}
  {x : VerifiableInference.Desc.First.Look.Place} {P : OnlineProverParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Tr X₀ Xh}
  {A : OnlineProverWithDescription FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Tr X₀ Xh} {G : Sides A.F A.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh}
  {more : List (String × Bool)}

/-- The family famG at the rows read at the description is the family onlineProversOfCommitter at the maker's prover. -/
theorem famG_sidesAt (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more) :
    famG Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 G) A.H =
      onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B (dataAtFiles flashProveData Z).P A.H :=
  (famG_eq Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 G) A.H).trans
    (by rw [sidesAt_prover, hd.ring])

/-- **Owed at the rows read at the description, at the committer's prover.** -/
theorem owed_atDescription {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (debts : RowDebtsP A G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord)) :
    Owed (descZ Zp Np cF) A.B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)
      (sidesAt hd.isTerm.2 G).mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord) :=
  owed_sidesAt hd.isTerm.2 (owed_of_kindsP hd (cmAlong (AZ Z) PadZ (holdZ Z)) 0 debts)

/-- **The online clause of zero knowledge at the maker's prover**, from the head, the row debts and owns. -/
theorem online_exact_of_honest (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (debts : RowDebtsP A G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord))
    (owns : G.owns = true)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    ExactOutsideStops
      ((HonestProvers.ofThreeProvers (proversOf hT hL (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B
                (dataAtFiles flashProveData Z).P A.H))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online.cleared
      (onlineSimulator Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 G) A.H n) := by
  rw [← famG_sidesAt Z Zp Np cF run₂ run₃ hd]
  exact online_exact_of_owed_atServed Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 G) A.H scope live
    hr hd.laid (owed_atDescription Z Zp Np cF hr hd debts)
    ((sidesAt_owns hd.isTerm.2 G).trans owns) hT hL n

/-- **The private stops' bound at the maker's prover.** -/
theorem online_stops_of_honest {zHid : ℝ≥0∞} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (hid : HidSmall (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B (dataAtFiles flashProveData Z).P A.H)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a) zHid)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (hL : Honest (protocolAtFiles Z).link (FullSizeMatrix × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) × ((protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)))
    (n : ℕ) :
    PrivateStopsAtMost
      ((HonestProvers.ofThreeProvers (proversOf hT hL (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B
                (dataAtFiles flashProveData Z).P A.H))).onlineAtCopy n)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w y)
      (workAtFiles Z).online zHid := by
  rw [← famG_sidesAt Z Zp Np cF run₂ run₃ hd] at hid ⊢
  exact online_stops_of_small_atValid Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 G) A.H hr hid
    hT hL n

/-- **The join at the maker's prover.** An implication: zero knowledge at the protocol, for the online prover onlineProversOfCommitter at A.H and the link's explicit prover, from: the
head; the row debts; owns; the measure of the online private stops; the work bits; the offline prover's two clauses and its table. -/
theorem zeroKnowledgeOnServedRequests_of_honest {zHid a : ℝ≥0∞}
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)
    (hd : AtHonest OnBytes.secondHashFunction Z D r Zp Np cF x P A G more)
    (debts : RowDebtsP A G ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 A.H)
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (ServedRequest committerCoinCountLessOne Z hr) instanceAsPlainRecord))
    (owns : G.owns = true)
    (hid : HidSmall (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B (dataAtFiles flashProveData Z).P A.H)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validB (ServedRequest committerCoinCountLessOne Z hr) w a) zHid)
    (faithful : (workAtFiles Z).Faithful) (two : TwoIndicesServeOneRequest Z hr)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (offlineSimulator : SimOf (protocolAtFiles Z).offline)
    (offlineTable : ∀ i r e, hT.ext (i, r, e) = (protocolAtFiles Z).encodeIndex i r)
    (offline : ExactOutsideStops hT (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y)
      (workAtFiles Z).offline.cleared offlineSimulator)
    (offlineStops : PrivateStopsAtMost hT (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles Z).validT w y)
      (workAtFiles Z).offline a) :
    ZeroKnowledgeOnServedRequests Z hr
      (HonestProvers.ofThreeProvers (proversOf hT (linkProverAtFiles committerCoinCountLessOne Z) (onlineProversOfCommitter Z Zp Np cF silInst run₂ run₃ A.B
                                            (dataAtFiles flashProveData Z).P A.H))) a 0 zHid := by
  rw [← famG_sidesAt Z Zp Np cF run₂ run₃ hd] at hid ⊢
  exact zeroKnowledgeOnServedRequests_of_owed Z Zp Np cF run₂ run₃ A.B (sidesAt hd.isTerm.2 G) A.H
    scope live hr hd.laid (owed_atDescription Z Zp Np cF hr hd debts)
    ((sidesAt_owns hd.isTerm.2 G).trans owns) hid faithful two hT offlineSimulator offlineTable offline
    offlineStops

end AtFiles

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.KindPays
#print axioms VerifiableInference.Compilation.sidesAt
#print axioms VerifiableInference.Compilation.sidesAt_prover
#print axioms VerifiableInference.Compilation.sidesAt_owns
#print axioms VerifiableInference.Compilation.owed_sidesAt
#print axioms VerifiableInference.Compilation.RowDebts
#print axioms VerifiableInference.Compilation.owed_of_kinds
#print axioms VerifiableInference.Compilation.RowDebtsP
#print axioms VerifiableInference.Compilation.owed_of_kindsP
#print axioms VerifiableInference.Compilation.RowDebts.toP
#print axioms VerifiableInference.Compilation.ready_of_head
#print axioms VerifiableInference.Compilation.famG_sidesAt
#print axioms VerifiableInference.Compilation.owed_atDescription
#print axioms VerifiableInference.Compilation.online_exact_of_honest
#print axioms VerifiableInference.Compilation.online_stops_of_honest
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_of_honest
