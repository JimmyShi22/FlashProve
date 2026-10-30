-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormAtFifty.lean: THE THREAD's CLAUSE `Form` BEHIND EACH OF THE
KIND K1's FIFTY LATER MEMBERS (every link's reads and digits), AT ProofFile's `lettersHead`, FROM THE
THREAD IN FRONT AND THE MEMBER's STEP. The first column `hF` of `owesS_head_form` at these numbers.
A join of laws that lie; no new argument. Under the library's head: a hypothesis.

  `hgs_head`        where the thread holds in front of such a member, the open link's frame bears
                    the group l and the plan's shape
  `k1_form_fifty`   the form at the next border

Limits. The step is a hypothesis: nothing here shows that the member accepts. Nothing on any
property. Full size, the format's second hash function.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K9FormBehind
import Johnson.Desc.ProofFile.Honest.Small.FormParts
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.IMR.AtReach
import Johnson.Desc.ProofFile.Honest.K1.Law.HeldAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.PubBehindAtFifty
import Johnson.Desc.First.Link.Law.PartFitsReached
import Johnson.Desc.ProofFile.Honest.K1.Law.DoorFactsAtAll
import Johnson.Desc.ProofFile.Honest.K1.Law.RideAtFifty
import Johnson.IMR.GroupHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT linksFull moreAll mgBase)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- Where the thread holds, the state is reached. -/
theorem reach_thr {b : Nat} {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E) :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (μ.st.input.x.pub, s) :=
  reach_of_made (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (ProofFile.startS Zp)
    μ.st.input.x.pub hb (fun _ e => e) hT.2.2.2.2.1

/-- The open link's frame's shape is the plan's, at a border up to 353, along the run. -/
theorem frameShape_thr {b : Nat} {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hb : b ≤ 353)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E) :
    ∀ Lk, s.link? = some Lk → Lk.check.frame.shape = h.𝔇.shape := by
  intro Lk hLk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hf := Meaning.K2.front_len h.scope h.reads O
  have hlen : b ≤ cF.blocksInOrder.length := by
    have := Meaning.Carry.flat_len h.scope h.reads O
    omega
  have hm := (ProofFile.Honest.Small.partsAt_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT).1
  rw [← LinkJoin.live_link hLk,
    Meaning.K2.liveShape_inFront h.scope h.reads O
      (reach_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT) hm (by rw [hf]; exact hb),
    K1.hDsh_atAll h O (K1.pin1_atAll h)]
  show Zp.first.shape = _
  rw [← O.first]
  exact K1.hs_atAll h O (K1.pin1_atAll h)

/-- **THE OPEN LINK's FRAME AT A MEMBER OF THE FIFTY**: its group and its shape, along the run. -/
theorem hgs_head {l : ℕ} (hl : l < 25) (d : Bool) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hlen : K1.noL l d ≤ cF.blocksInOrder.length)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (K1.noL l d) k s μ E) :
    ∀ L, s.link? = some L → L.check.frame.group = h.𝔇.N.groupAt l ∧
      L.check.frame.shape = (Sound.d13 h.𝔇).shape := by
  intro L hL
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hR := reach_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT
  obtain ⟨-, rs, cols, f⟩ := hR.fold
  have hb : 14 * l + 2 ≤ K1.noL l d ∧ K1.noL l d ≤ 14 * l + 14 + (if l = 24 then 2 else 0) := by
    by_cases e : l = 24
    · subst e
      cases d <;> decide
    · cases d <;> simp only [K1.noL, IM.k1Ix, if_neg e, Bool.false_eq_true, if_false, if_true] <;> omega
  refine ⟨?_, frameShape_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w ?_ hT L hL⟩
  · have eG : h.𝔇.N.groupAt l = l := by rw [head_N_is h]; rfl
    rw [eG]
    exact (Meaning.K2.group_is h.scope h.reads O hl hb.1 hb.2 f L hL).2
  · have h3 := hb.2
    split at h3 <;> omega

/-- **THE FORM BEHIND A MEMBER OF THE FIFTY.** -/
theorem k1_form_fifty (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {l : ℕ}
    (hl : l < 25) (d : Bool) {blk : Block TS ProofFile.Cl} {k : Coins Bk} {s s' : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hblk : cF.blocksInOrder[K1.noL l d]? = some blk)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l d) k s
      m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (K1.noL l d + 1) k s' y.2 := by
  have hT' := hT.1
  have hF : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (K1.noL l d) k s m :=
    hT'.2.2.1
  have hlen : K1.noL l d ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hR := reach_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT'
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hbk : First.bookAt h.𝔇.N (First.flatPlacesOf linksFull true)[K1.noL l d]? s = true :=
    (ProofFile.Honest.Small.partsAt_of_thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT').2.book
  refine form_behind_of_ew h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hS hF
    (mark_later_head h hl d hblk 0 hyes)
    (xk_later_head h hl d hblk _ hbase_mgBase m.st.input.x.pub 0
      (hgs_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl d hlen hT')
      (fun e1 e2 => by subst e1; subst e2; exact hR) hyes h0
      (xk_ew_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF))
    (samples_later_head h hl d hblk _ (head_held_smp h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _ 0
      hR (by rw [IM.placesW_full, ← head_N_is h]; exact hbk) hyes
      (held_w_front h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF)) ?_
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, Xh, arrs, he, hu⟩ := K1.k01_flat h.scope h.reads O l hl d
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hblk)
  exact pubP_later_all h.𝔇.pubD (mgBase : First.Meaning ProofFile.InstPub WtF).pub (P5J.At.X Zp) h.𝔇.sent
    h.𝔇.d1 h.𝔇.rw13 h.𝔇.A1 h.𝔇.cr1 _ (head_pubP_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_pub_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) _ m.st.input.x.pub 0 Zp Bs.G₀ l hl d
    Xh arrs e hu s s' hyes
    (xk_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF)
    (fun mm hm => pubP_of_form (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hF _ hm)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.hgs_head
#print axioms ProofFile.Honest.K1.k1_form_fifty
