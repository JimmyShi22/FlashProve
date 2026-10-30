-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/OpenItemsAtTheDoor.lean: THE ITEMS OPEN AT THE LAST CHAIN's
START. The last chain opens five items: the index masks' pin, W's pin, the row (Eval), the row
(Dot) and Omega's pin. Three of them stand open at the first chain's end and one at the shared
chain's end, and they come over by what each reads. (Dot) stands at neither end: it is made from
the verifier's two folds and the honest messages (AtFullSide/K13/DotAtTheDoor.lean).

  strs_first, strs_shared   what the last chain's tables show is what the earlier chain's show
  ends_at_door   at the letters of door_heads_walk, ends is the two earlier chains' last states
  seat_at_door   what an item of the last chain is said of, at its start
  items_at_door  the premise hItems of door_heads_walk

What these are. Conditional lemmas on our own definitions. None is one of the library's goals.
They say nothing of soundness, completeness or hiding of the protocol.

Limits.
  * The five items are asked of items_at_door as one premise.
  * None of the premises is shown here of any run.
-/
import Johnson.Desc.ProofFile.Honest.Thread.EndsAtHeads
import Johnson.Desc.ProofFile.Honest.Thread.PointOfTheSharedChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-! ## 1 The tables at the door -/

/-- Two lists of tables show the same stored table, and the same trees of the numbers from lo up to
below hi. -/
def SameIn (lo hi : Nat) (y y' : VerifiableInference.Desc.Strs) : Prop :=
  y.cell = y'.cell ∧ ∀ j, lo ≤ j → j < hi → y.col j = y'.col j

/-- **The last chain shows the first chain's trees as the first chain does.** -/
theorem strs_first (item n₁ n₂ : Nat) (E₁ E₂ : Env) :
    SameIn 0 n₁ (Env.strs item (srcAt 0 n₁ n₂) E₁)
      (Env.strs item (srcAt 2 n₁ n₂) (envThird E₁ E₂)) := by
  refine ⟨rfl, fun j _ hj => funext fun x => ?_⟩
  simp [Env.strs, srcAt, hj, envThird]

/-- **The last chain shows the shared chain's trees as the shared chain does**, where the two
stored tables are one. -/
theorem strs_shared (item n₁ n₂ : Nat) (E₁ E₂ : Env) (hst : E₂.stored = E₁.stored) :
    SameIn n₁ (n₁ + n₂) (Env.strs item (srcAt 1 n₁ n₂) E₂)
      (Env.strs item (srcAt 2 n₁ n₂) (envThird E₁ E₂)) := by
  refine ⟨by simp [Env.strs, envThird, hst], fun j h₁ h₂ => funext fun x => ?_⟩
  have hn : ¬ j < n₁ := Nat.not_lt.2 h₁
  simp [Env.strs, srcAt, hn, h₁, h₂, envThird]

end ProofFile.Honest

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS)
open VerifiableInference.Desc.Last (MeaningL PromMeaningL ItemL startLast)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (Item)
open Desc.K14.Law (OmegaIs DotEq)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {p₀ : VerifiableInference.Desc.First.Look.Place}

local notation "𝔽" => F0T OnBytes.secondHashFunction Zp Np cF

/-! ## 2 What an item of the last chain is said of -/

/-- **At the three terms and the letters, the function ends is the two earlier chains' last
states.** The lines of door_heads_walk's proof, as a statement. -/
theorem ends_at_door (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF p₀) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X₀ X Wt₂ : Type} [Inhabited TS] [Inhabited Desc.K14.St]
    (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop)
    (N : NumbersS)
    (Mg₂ : Common W₀ Rc OnBytes.TableKey → MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt₂)
    (shape : Nat → Desc.K14.St → Bool) (nothingLeft : Desc.K14.St → Bool)
    (order₂ : Desc.K14.St → Prop)
    (wit₂ : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt₂)
    (table₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
      Place × Table)
    (fixed₂ : Fmt.TreeSource → Nat) (Vd₂ : Common W₀ Rc OnBytes.TableKey → Prop)
    (Rd₂ : Nat → Common W₀ Rc OnBytes.TableKey → Desc.K14.St → Prop)
    (Kp₂ : Place → Desc.K14.St → Desc.K14.St → Prop)
    {m₀₁ : Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {m₀₂ : Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀}
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}
    {T₁ : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
    {T₂ : Thread Bk Desc.K14.St ProofFile.Cl Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey}
    {ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
      (ProofFile.InstPub × TS) × Desc.K14.St}
    (hR : ready (𝔽) Bk H w₀ rc ξ k = .ok R)
    (t₁ : T₁ = (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread)
    (t₂ : T₂ = (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
      fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread)
    (tE : ends = fun k w hd =>
      ((w.x.pub,
        (endsBy T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length T₂ (SaidWalk T₂ BaseNil m₀₂)
          (𝔽).shared.blocksInOrder.length id
          (fun w => ⟨w.w₀, w.rc, H.key w.x⟩) k w hd).1),
        (endsBy T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length T₂ (SaidWalk T₂ BaseNil m₀₂)
          (𝔽).shared.blocksInOrder.length id
          (fun w => ⟨w.w₀, w.rc, H.key w.x⟩) k w hd).2))
    (ho₁ : ∀ b, b ≤ (𝔽).first.blocksInOrder.length → T₁.opensAvailable b = true)
    (ho₂ : ∀ b, b ≤ (𝔽).shared.blocksInOrder.length → T₂.opensAvailable b = true)
    (hd₁ : ∀ k b, b ≤ (𝔽).first.blocksInOrder.length → ∀ m, WalkedTo T₁ m₀₁ k b m → DepthsAt T₁ b k m)
    (hd₂ : ∀ k b, b ≤ (𝔽).shared.blocksInOrder.length → ∀ m, WalkedTo T₂ m₀₂ k b m → DepthsAt T₂ b k m) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length k e₂ m₂ E₂ →
      ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((ξ.pub, e₁), e₂) := by
  obtain ⟨-, tr, -, hown, hcom, -, -, -⟩ := ready_ok hR
  have hξ : R.own.x = ξ := by rw [hown]
  have hc : R.common = ⟨R.own.w₀, R.own.rc, H.key R.own.x⟩ := by rw [hcom, hown]
  have hf₁ : ∀ k w hd s s', T₁.begun k w hd s → T₁.begun k w hd s' → s = s' := by
    rw [t₁]
    exact fun _ _ _ s s' a b => Eq.trans (a : s = _) (Eq.symm (b : s' = _))
  have hf₂ : ∀ k w hd s s', T₂.begun k w hd s → T₂.begun k w hd s' → s = s' := by
    rw [t₂]
    exact fun _ _ _ s s' a b => Eq.trans (a : s = _) (Eq.symm (b : s' = _))
  have hE := endsAre_endsBy T₁ (SaidWalk T₁ BaseNil m₀₁) (𝔽).first.blocksInOrder.length T₂
    (SaidWalk T₂ BaseNil m₀₂) (𝔽).shared.blocksInOrder.length id
    (fun w : Local W₀ Rc ProofFile.Inst Tr => (⟨w.w₀, w.rc, H.key w.x⟩ : Common W₀ Rc OnBytes.TableKey))
    (oneState_walk T₁ hf₁ ho₁ hd₁) (oneState_walk T₂ hf₂ ho₂ hd₂)
  intro e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂
  have h1 := u₁.1
  have h2 := u₂.1
  unfold Thr at h1 h2
  subst t₁ t₂
  have i₁ : m₁.st.input = R.own := h1.2.2.2.2.2.2.1
  have i₂ : m₂.st.input = ⟨R.own.w₀, R.own.rc, H.key R.own.x⟩ := h2.2.2.2.2.2.2.1.trans hc
  have e := hE k R.own e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ i₁ i₂
  have a0 : R.own.x.pub = ξ.pub := congrArg (fun z => z.pub) hξ
  have a1 := congrArg Prod.fst e
  have a2 := congrArg Prod.snd e
  subst tE
  exact Prod.ext (Prod.ext a0 a1) a2

/-! ## 3 The five items -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X Cells Tok M Wt₂ Wt₃ : Type}
  {H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}
  {ξ : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}
  (L₁ : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub Cells Tok M)
  (L₂ : SharedThread.Letters Bk Desc.K14.St ProofFile.Cl W₀ Rc OnBytes.TableKey X₀
    (ProofFile.InstPub × TS) Wt₂)
  (L₃ : LastThread.Letters Bk Desc.K14.St VerifiableInference.Desc.Third.S₃ ProofFile.Cl W₀ Rc ProofFile.Inst
    Tr X (ProofFile.InstPub × TS) Wt₃)
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop}
  {c₁ c₂ : Nat}

/-- **What an item of the last chain is said of, at its start.** -/
theorem seat_at_door (hah₁ : L₁.thread.ahead = []) (hah₂ : L₂.thread.ahead = [])
    (hah : L₃.ahead = declsTo L₁.thread.bs c₁ ++ declsTo L₂.thread.bs c₂)
    {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    {e₂ : Desc.K14.St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : Thr L₁.thread c₁ k e₁ m₁ E₁) (u₂ : Thr L₂.thread c₂ k e₂ m₂ E₂)
    (hends : L₃.ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((ξ.pub, e₁), e₂))
    (s : VerifiableInference.Desc.Third.S₃) :
    L₃.thread.seat k (R.start₃ H m₁ m₂) s = (((ξ.pub, e₁), e₂), s) := by
  have hF₁ := u₁.2.1
  have hF₂ := u₂.2.1
  unfold Thread.Fit at hF₁ hF₂
  rw [hah₁, List.nil_append] at hF₁
  rw [hah₂, List.nil_append] at hF₂
  have l₁ := drawsFit_length _ _ hF₁
  have l₂ := drawsFit_length _ _ hF₂
  have hfr : L₃.thread.front = (m₁.st.heard ++ m₂.st.heard).length := by
    show L₃.ahead.length = _
    rw [hah, List.length_append, List.length_append, l₁, l₂]
  show (L₃.ends k R.own ((m₁.st.heard ++ m₂.st.heard).take L₃.thread.front), s) = _
  rw [hfr, List.take_length, hends]

/-- **The premise hItems of door_heads_walk, from the five.** Each of the five is asked where the two
earlier threads hold, at every continuation. -/
theorem items_at_door (hah₁ : L₁.thread.ahead = []) (hah₂ : L₂.thread.ahead = [])
    (hah : L₃.ahead = declsTo L₁.thread.bs c₁ ++ declsTo L₂.thread.bs c₂)
    (hends : ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS L₁.thread S₁ c₁ k e₁ m₁ E₁ →
      ThrS L₂.thread S₂ c₂ k e₂ m₂ E₂ →
      L₃.ends k R.own (m₁.st.heard ++ m₂.st.heard) = ((ξ.pub, e₁), e₂))
    (five : ∀ e₁ m₁ E₁ e₂ m₂ E₂, ThrS L₁.thread S₁ c₁ k e₁ m₁ E₁ →
      ThrS L₂.thread S₂ c₂ k e₂ m₂ E₂ → ∀ s₃ ds, ∀ i ∈ startLast,
        VerifiableInference.Desc.Last.ItemL.holds L₃.N (L₃.Mg R.own) L₃.ML i (ξ.pub, e₁) e₂ s₃
          (L₃.thread.strs (envThird E₁ E₂)) (L₃.wit k R.own (m₁.st.heard ++ m₂.st.heard ++ ds))) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS L₁.thread S₁ c₁ k e₁ m₁ E₁ →
      ThrS L₂.thread S₂ c₂ k e₂ m₂ E₂ →
      L₃.thread.Items (L₃.thread.opened 0) k s₃ (R.start₃ H m₁ m₂) (envThird E₁ E₂) := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ ds i hi
  have hs := seat_at_door L₁ L₂ L₃ (H := H) hah₁ hah₂ hah u₁.1 u₂.1
    (hends e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂) s₃
  show VerifiableInference.Desc.Last.ItemL.holds L₃.N (L₃.Mg R.own) L₃.ML i
    (L₃.thread.seat k (R.start₃ H m₁ m₂) s₃).1.1 (L₃.thread.seat k (R.start₃ H m₁ m₂) s₃).1.2
    (L₃.thread.seat k (R.start₃ H m₁ m₂) s₃).2 (L₃.thread.strs (envThird E₁ E₂))
    (L₃.wit k R.own (m₁.st.heard ++ m₂.st.heard ++ ds))
  rw [hs]
  exact five e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ s₃ ds i hi

/-- **An item that stands open at the first chain's end**, at what the first chain's thread says of
it. -/
theorem first_item_at_end {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (hpub : L₁.pubOf m₁.st.input.x = ξ.pub) (u₁ : Thr L₁.thread c₁ k e₁ m₁ E₁) {i : Item}
    (hi : i ∈ L₁.thread.opened c₁) (ds : List Fmt.Drawn) :
    Item.holds L₁.N (L₁.mg m₁.st.input) i (ξ.pub, e₁) (L₁.thread.strs E₁)
      (L₁.Q.wit k m₁.st.input (m₁.st.heard ++ ds)) := by
  have h := u₁.2.2.2.1 ds i hi
  have e : L₁.thread.seat k m₁ e₁ = (ξ.pub, e₁) := by
    show (L₁.pubOf m₁.st.input.x, e₁) = _
    rw [hpub]
  have h' : Item.holds L₁.N (L₁.mg m₁.st.input) i (L₁.thread.seat k m₁ e₁) (L₁.thread.strs E₁)
      (L₁.Q.wit k m₁.st.input (m₁.st.heard ++ ds)) := h
  rw [e] at h'
  exact h'

/-- **Omega's pin at the shared chain's end.** -/
theorem shared_pin_at_end {e₂ : Desc.K14.St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀}
    {E₂ : Env} (u₂ : Thr L₂.thread c₂ k e₂ m₂ E₂)
    (hi : ItemS.pin .oOmega ∈ L₂.thread.opened c₂) (ds : List Fmt.Drawn) :
    (ItemS.pin .oOmega).holdsSh L₂.N (L₂.Mg m₂.st.input) e₂ (L₂.thread.strs E₂)
      (L₂.wit k m₂.st.input (m₂.st.heard ++ ds)) :=
  u₂.2.2.2.1 ds _ hi

end

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.strs_first
#print axioms ProofFile.Honest.strs_shared
#print axioms ProofFile.Honest.FirstThread.ends_at_door
#print axioms ProofFile.Honest.FirstThread.seat_at_door
#print axioms ProofFile.Honest.FirstThread.items_at_door
#print axioms ProofFile.Honest.FirstThread.first_item_at_end
#print axioms ProofFile.Honest.FirstThread.shared_pin_at_end
