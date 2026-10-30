-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/DoorStart.lean: THE SECOND CHAIN's START RETURNS, AT THE FIRST CHAIN's AND THE SHARED
CHAIN's LAST BORDERS: the field doorYes of FromThreadsJ at lettersHead's thread, with J₁ the shape's.

  start_of_out: startAtEnds returns, from firstOfS, firstOutFrom and the tests on codes and roots.
  **doorYes_at_head**: under the head, one closed line at the stored files (hc, hcl, as first_out_at_end), and
  three premises on the shared thread: T₂.bs, T₂.ahead and its begun.

Limits. hc and hcl are premises: the closed line at the written border. Nothing on soundness, completeness
or hiding.
-/
import Johnson.AtFull.Shape.Scope.DoorFirst
import Johnson.AtFull.Shape.Scope.DoorShared
import Johnson.AtFull.Shape.Scope.EndAtScope
import AtFullSide.K13.DoorYesAtEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Third (P₁₄ startAtEnds firstOfS sharedOfEnd start₃E firstOutFrom start₃
  rootsB)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest (Thread ProverCoinCounts Coins Mid Prover Local Common Thr ThrS shapeJ)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

/-- **The second chain's start returns, from its tests.** -/
theorem start_of_out (p : P₁₄) {Xp : Type} (x : Xp) {e₁ : TS} {d : OnBytes.Proof.SharedEnd}
    {f : VerifiableInference.Desc.Third.FirstEnd₃} {o : VerifiableInference.Desc.Third.FirstOut}
    (hf : firstOfS e₁ = some f)
    (ho : firstOutFrom p.S f.st f.book f.roots f.w f.own f.mask f.pending = some o)
    (hl : (p.codes.lengthsOk && OnBytes.linOk p.codes p.S) = true)
    (h₁ : e₁.st.codes = p.codes) (h₂ : d.st.codes = p.codes)
    (hb : rootsB e₁.roots e₁.book = true) :
    ∃ s, startAtEnds p x e₁ d = .ok s := by
  have ef : f.st = e₁.st ∧ f.book = e₁.book ∧ f.roots = e₁.roots := by
    unfold firstOfS at hf
    cases he : e₁.firstEnd? with
    | none =>
      rw [he] at hf
      cases hf
    | some e =>
      rw [he] at hf
      obtain rfl := Option.some.inj hf
      exact ⟨rfl, rfl, rfl⟩
  have eo : o.st = f.st ∧ o.book = f.book ∧ o.roots = f.roots := by
    unfold firstOutFrom at ho
    split at ho
    · split at ho
      · dsimp only at ho
        split at ho
        · obtain rfl := Option.some.inj ho
          exact ⟨rfl, rfl, rfl⟩
        · cases ho
      · cases ho
    · cases ho
  show ∃ s, (match firstOfS e₁ with
    | none => .error "the first chain's end names no W"
    | some f => start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending
        (sharedOfEnd d)) = (.ok s : Except String VerifiableInference.Desc.Third.S₃)
  rw [hf]
  show ∃ s, start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending
    (sharedOfEnd d) = .ok s
  obtain ⟨s₀, e4⟩ : ∃ s₀, start₃ p.codes o (sharedOfEnd d) = some s₀ := by
    unfold start₃
    split
    · exact ⟨_, rfl⟩
    · rename_i hne
      exfalso
      apply hne
      rw [eo.1, eo.2.1, eo.2.2, ef.1, ef.2.1, ef.2.2]
      have h₂' : (sharedOfEnd d).st.codes = p.codes := h₂
      simp [h₁, h₂', hb]
  unfold start₃E
  simp only [hl, Bool.not_true, Bool.false_eq_true, if_false, ho, e4]
  exact ⟨_, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **THE FIELD doorYes AT lettersHead's THREAD.** -/
theorem doorYes_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {c : ShA} (hc : (shapeL (LWn X₀)).run 358 startShA = .ok c)
    (hcl : endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape c = true)
    {Bk : ProverCoinCounts} {W₀ Rc Tr X₀' X' : Type}
    (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀' X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    {T₂ : Thread Bk Desc.K14.St ProofFile.Cl Empty (Common W₀ Rc OnBytes.TableKey) X₀' OnBytes.TableKey}
    {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop}
    {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀' → Prop}
    (ξ : ProofFile.Inst) (k : Coins Bk)
    (hbs : T₂.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) (hah : T₂.ahead = [])
    (hbeg₂ : ∀ k w hd s₀, T₂.begun k w hd s₀ → ∃ p, s₀ = (F0T OnBytes.secondHashFunction Zp Np cF).start₂ p) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread S₁
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k e₂ m₂ E₂ →
      shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length e₁ →
      ∃ s₃, (F0T OnBytes.secondHashFunction Zp Np cF).start₃ ξ.pub e₁ e₂ = .ok s₃ := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂ j₁
  have hf := AtFullSide.K13.fin_at_first_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ u₁.1
  have hM : T₂.Made T₂.bs.length k e₂ m₂ E₂ := by
    rw [hbs]
    exact u₂.1.2.2.2.2.1
  have ht := AtFullSide.K13.tested_at_shared_end (Zp := Zp) (Np := Np) (cF := cF) T₂ hbs hah hM
  have hst : ∃ d, Desc.K14.ended e₂ = some d ∧ d.st = e₂.st := by
    unfold Desc.K14.ended
    rw [if_pos ht]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨d, hd, eds⟩ := hst
  have hl : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = 358 := flat_len h
  rw [hl] at j₁
  obtain ⟨-, f, hfo, o, ho⟩ := first_out_at_end h hB hX₀ hc hcl j₁
  have ends := first_thr_ends h (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread rfl
    (fun v => v.x.pub) (fun _ _ _ _ h0 => h0)
    (fun _ _ s _ hF => by
      have t : s.failed.isNone = true := hF.1
      simpa using t) u₁.1
  have c₂ := shared_thr_codes T₂ hbs hbeg₂ u₂.1
  obtain ⟨s, hs⟩ := start_of_out (ProofFile.pAt Zp) ξ.pub hfo ho (door_public h).1 ends.1
    (by rw [eds]; exact c₂) ends.2
  exact ⟨s, (ProofFile.fileDescBy_start₃_iff OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (ProofFile.sharedAt Zp Np)
    (P2Third.secondSeatOf Zp Np) (fun s => s) (ProofFile.startS Zp) cF ξ.pub e₁ e₂ s).2
    ⟨hf, d, hd, hs⟩⟩

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.start_of_out
#print axioms Johnson.AtFull.Shape.Scope.doorYes_at_head
