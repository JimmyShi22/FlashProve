-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/DotAtTheDoor.lean: THE ROW (Dot) AT THE DOOR BETWEEN THE CHAINS, AT THE LIBRARY's OWN
DESCRIPTION. (Dot) says that W at the shared point psi is the row weights g applied to Omega. The
last chain reads g off the first chain's last state and psi off the shared chain's last state.
Here both are laws on the verifier's folds: g is what the filling of W makes of the challenges
heard on the first chain, psi is the first challenge heard on the shared chain. So the row holds
wherever the honest messages W and Omega are what the prover makes of these two.

  gMade          the row weights of which the prover makes W, at the challenges heard
  g_at_door      the reader gLaid at the first chain's end is gMade of the challenges heard
  point_at_door  psi at the shared chain's end is pointHeard of the challenges heard
  dot_at_the_door   (Dot) at the last chain's start, from these two and what the witness holds
  five_at_door   the five items of the last chain's start
  items_at_letters   the premise hItems of door_heads_walk at the three terms

What these are. Conditional lemmas under the library's one hypothesis at the full size, h, and a
base. None is one of the library's goals. They say nothing of soundness, completeness or hiding.

Limits.
  * hW and hO are premises: the witness holds W's text wVec and Omega's text omegaAtE, both at the one
    letter Wt, the index's weights. That the prover's messages are these texts is not said here.
    Both texts are read at the first chain's shape: that the shared chain's is that shape is not said.
  * The shape is asked to split the row (hS). hbl: the kind's eight blocks can be made.
  * dot_at_the_door's hdot speaks of every pair q, e. A meaning whose vectors read the pair cannot meet
    it. five_at_door asks (Dot) at the one pair, hDot.
  * Of the other four items only how they come over is stated: cI, cV, cE, cO, with oI, oV, oE, oO that
    they stand open at the two ends, and Alone, what (Eval) needs beside wrow. hv₂, hst and the
    equations on the numbers are premises on the letters; item is 0 at the shared chain's letters.
  * y₀: any frame and any string of it: an idle argument of the library's lemma.
-/
import AtFullSide.K13.GAtFirstEnd
import Johnson.Desc.ProofFile.Honest.Thread.OpenItemsAtTheDoor
import Johnson.Desc.ProofFile.Honest.Thread.DotOfTheTexts
import Johnson.Desc.Sound.AtOcEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K13
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block foldBlocks OpenedColumn)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (EvalLaid laidOf_ok)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Sound (MsgT)
open Desc.K14 (p14Of beforePointOf)
open Desc.K14.Law (OmegaIs DotEq gLaid gLaid_is)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- The row weights of which the prover makes W, at the challenges heard. -/
noncomputable def gWords (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (x : ProofFile.Inst) (hd : List Fmt.Drawn) :
    List OnBytes.Tensor :=
  wG Zp.first.lin (wHeard Zp) (pileAnyK3 Zp Bs.G₀) x (hd.take (wHeard Zp))

/-- The same, entry by entry. -/
noncomputable def gMade (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (x : ProofFile.Inst) (hd : List Fmt.Drawn)
    (y : Nat) : OnBytes.Slice.GE :=
  ((gWords Zp Bs x hd).map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **The first law on the folds.** -/
theorem g_at_door (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {P₀ P₁ : Type}
    (get : P₁ → P₀ × TS) {q : P₁} {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k s m
      En)
    (hq : (get q).2 = s) (hR : ReplyIs ProofFile.Inst.asked m.st.input.x s)
    (hE : EvalLaid (whereOf Zp) s) :
    gLaid (whereOf Zp) get q = gMade Zp Bs m.st.input.x m.st.heard := by
  obtain ⟨Dv, hD, -, hrows, -⟩ := laidOf_ok hE
  funext y
  rw [gLaid_is (whereOf Zp) get q Dv (by rw [hq]; exact hD) y]
  unfold gMade gWords
  rw [k13_g_at_first_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Bs hB k s m En hT hR Dv.row
    hrows]

end

/-- **The second law on the folds**, at the shared chain of the library's description. -/
theorem point_at_door {Bk : ProverCoinCounts} {V W X Pb : Type}
    (T : Thread Bk Desc.K14.St ProofFile.Cl V W X Pb)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hbl : Desc.K14.blocks (p14Of Zp.p.chains (beforePointOf Np)) =
      some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplitNeeded = true)
    (hbs : T.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder) (hah : T.ahead = [])
    {k : Coins Bk} {s : Desc.K14.St} {m : Mid W X} {E : Env}
    (hM : T.Made T.bs.length k s m E) :
    s.loc.psiSh = Door.pointHeard m.st.heard :=
  Door.point_at_made T Zp.p.chains (p14Of Zp.p.chains (beforePointOf Np)) b1 b2 b3 b4 b5 b6 b7 b8
    (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hbl hS
    (Door.point_kept_tests Np) (Door.point_kept_last _) hbs hah hM

section
open VerifiableInference.Desc.Last (ItemL startLast)
open VerifiableInference.Desc.Shared (ItemS)
open VerifiableInference.Desc.First (Item)
open ProofFile.Honest.FirstThread (lettersHead Letters)

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Tr X₀ X' Wt₂ Wt₃ : Type}
  (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (L₂ : SharedThread.Letters Bk Desc.K14.St ProofFile.Cl W₀ Rc OnBytes.TableKey X₀
    (ProofFile.InstPub × TS) Wt₂)
  (L₃ : LastThread.Letters Bk Desc.K14.St VerifiableInference.Desc.Third.S₃ ProofFile.Cl W₀ Rc ProofFile.Inst
    Tr X' (ProofFile.InstPub × TS) Wt₃)
  {ξ : ProofFile.Inst} {k : Coins Bk} {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X'}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop}

/-- **(Dot) at the last chain's start, from the two laws on the folds.** Wt, rd: the index's weights and
the table's random values, which both messages read. get, Om, Wv, gR: the letters of the meaning's
field dot. hdot: that field says (Dot) so. hW, hO: the witness holds W's and Omega's texts, at the
two earlier threads' stands. hlen: the point has the shape's number of coordinates. -/
theorem dot_at_the_door (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {F : VerifiableInference.Desc.Sound.Frame} (y₀ : F.E.Str)
    (hξ : R.own.x = ξ) (hb₀ : b₀ ≤ cF.blocksInOrder.length)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hbl : Desc.K14.blocks (p14Of Zp.p.chains (beforePointOf Np)) =
      some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : (p14Of Zp.p.chains (beforePointOf Np)).S.sharedSplitNeeded = true)
    (hbs : L₂.thread.bs = (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
    {P₀ : Type} (get : ProofFile.InstPub × TS → P₀ × TS) (hg : ∀ q, (get q).2 = q.2)
    (Wt : Weights) (rd : TableRand)
    (hroom : Zp.first.lin.matrixRows * 2 ^ Zp.first.lin.kLo ≤ Zp.first.lin.fold.index.plain)
    (Om Wv : Wt₃ → Nat → OnBytes.Slice.GE)
    (gR : ProofFile.InstPub × TS → Nat → OnBytes.Slice.GE)
    (hgR : ∀ q, EvalLaid (whereOf Zp) q.2 → gR q = gLaid (whereOf Zp) get q)
    (hdot : ∀ q e y v, DotEq Zp.first.lin.matrixRows Zp.first.lin.kCol (gR q) (Om v)
      (e.loc.psiSh.map OnBytes.Model.Reading.gl.val) (Wv v) → ((L₃.Mg R.own).dot q e y v))
    {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    {e₂ : Desc.K14.St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread S₁
      cF.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : ThrS L₂.thread S₂ L₂.thread.bs.length k e₂ m₂ E₂) (ds : List Fmt.Drawn)
    (hlen : (Door.pointHeard m₂.st.heard).length = Zp.first.lin.kCol)
    (hW : ∀ c < 2 ^ Zp.first.lin.kCol, Wv (L₃.wit k R.own (m₁.st.heard ++ m₂.st.heard ++ ds)) c =
      wVec Zp.first.lin Wt (gWords Zp Bs ξ m₁.st.heard) c)
    (hO : ∀ y < Zp.first.lin.matrixRows,
      Om (L₃.wit k R.own (m₁.st.heard ++ m₂.st.heard ++ ds)) y = OnBytes.Model.Reading.gl.val
        (Desc.K14.Honest.omegaAtE Zp.first.lin (Door.pointHeard m₂.st.heard)
          (ProofFile.Honest.K14.rowsOf Zp.first.lin Wt rd) y)) (y : Strs) :
    (L₃.Mg R.own).dot (ξ.pub, e₁) e₂ y (L₃.wit k R.own (m₁.st.heard ++ m₂.st.heard ++ ds)) := by
  have t₁ := u₁.1
  have hah₂ : L₂.thread.ahead = [] := rfl
  have i₁ : m₁.st.input = R.own := t₁.2.2.2.2.2.2.1
  have hx : m₁.st.input.x = ξ := by rw [i₁]; exact hξ
  have hr : ReplyIs ProofFile.Inst.asked m₁.st.input.x e₁ :=
    ProofFile.Honest.FirstThread.head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own hb₀
      t₁.2.2.2.2.2.1
  have hE := k13_evalLaid_at_end h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own y₀ k e₁ m₁ E₁ t₁
  have hgl : gLaid (whereOf Zp) get (ξ.pub, e₁) = gMade Zp Bs ξ m₁.st.heard := by
    have a := g_at_door h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own Bs hB get
      (q := (ξ.pub, e₁)) t₁ (hg _) hr hE
    rw [hx] at a
    exact a
  have hpt := point_at_door (Zp := Zp) (Np := Np) (cF := cF) L₂.thread b1 b2 b3 b4 b5 b6 b7 b8 hbl
    hS hbs hah₂ u₂.1.2.2.2.2.1
  refine hdot _ _ _ _ ?_
  rw [hgR (ξ.pub, e₁) hE, hgl, hpt]
  exact Door.dot_of_texts Zp.first.lin Wt rd _ _ hlen hroom _ _ hW hO

/-- **THE FIVE ITEMS OF THE LAST CHAIN's START**: three come over from the first chain's end and one
from the shared chain's; (Dot) is hDot, at the one pair of ends. cI, cV, cE, cO: how each of the
four comes over: what it says at the earlier chain's tables and witness it says at the last chain's,
where the two show the same trees of the chain that it reads. -/
theorem five_at_door (hξ : R.own.x = ξ)
    (hp₁ : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).pubOf ξ = ξ.pub)
    (hi₃ : L₃.item = item) (hn₃ : L₃.n₁ = n₁) (hm₃ : L₃.n₂ = n₂)
    (hi₂ : L₂.item = item) (hn₂ : L₂.n₁ = n₁) (hm₂ : L₂.n₂ = n₂)
    (hv₂ : ∀ v, L₂.valid v → v = R.common)
    (hst : ∀ i x, L₂.stored R.common i x = H.storedWords R.own.w₀ R.own.rc i x)
    (oI : Item.pinI ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.opened
      cF.blocksInOrder.length)
    (oV : Item.pinV ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.opened
      cF.blocksInOrder.length)
    (oE : Item.wrow ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.opened
      cF.blocksInOrder.length)
    (oO : ItemS.pin .oOmega ∈ L₂.thread.opened L₂.thread.bs.length)
    (cI : ∀ e₁ e₂ s₃ y y' hd, SameIn 0 n₁ y y' →
      Item.holds (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).N
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).mg R.own) Item.pinI
        (ξ.pub, e₁) y (Q.wit k R.own hd) →
      ItemL.holds L₃.N (L₃.Mg R.own) L₃.ML .pinI (ξ.pub, e₁) e₂ s₃ y' (L₃.wit k R.own hd))
    (cV : ∀ e₁ e₂ s₃ y y' hd, SameIn 0 n₁ y y' →
      Item.holds (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).N
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).mg R.own) Item.pinV
        (ξ.pub, e₁) y (Q.wit k R.own hd) →
      ItemL.holds L₃.N (L₃.Mg R.own) L₃.ML .pinV (ξ.pub, e₁) e₂ s₃ y' (L₃.wit k R.own hd))
    (Alone : TS → Prop)
    (cE : ∀ e₁ e₂ s₃ y y' hd, Alone e₁ → SameIn 0 n₁ y y' →
      Item.holds (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).N
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).mg R.own) Item.wrow
        (ξ.pub, e₁) y (Q.wit k R.own hd) →
      ItemL.holds L₃.N (L₃.Mg R.own) L₃.ML .ev (ξ.pub, e₁) e₂ s₃ y' (L₃.wit k R.own hd))
    (hnear : L₃.near = roundsTo cF.blocksInOrder cF.blocksInOrder.length)
    (cO : ∀ e₁ e₂ s₃ y y' h₁ h₂, h₁.length = L₃.near → SameIn n₁ (n₁ + n₂) y y' →
      (ItemS.pin .oOmega).holdsSh L₂.N (L₂.Mg R.common) e₂ y (L₂.wit k R.common h₂) →
      ItemL.holds L₃.N (L₃.Mg R.own) L₃.ML .pinO (ξ.pub, e₁) e₂ s₃ y'
        (L₃.wit k R.own (h₁ ++ h₂)))
    {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E₁ : Env}
    {e₂ : Desc.K14.St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₁ : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread S₁
      cF.blocksInOrder.length k e₁ m₁ E₁)
    (u₂ : ThrS L₂.thread S₂ L₂.thread.bs.length k e₂ m₂ E₂) (hAl : Alone e₁)
    (hDot : ∀ ds y, (L₃.Mg R.own).dot (ξ.pub, e₁) e₂ y
      (L₃.wit k R.own (m₁.st.heard ++ m₂.st.heard ++ ds))) :
    ∀ s₃ ds, ∀ i ∈ startLast,
      ItemL.holds L₃.N (L₃.Mg R.own) L₃.ML i (ξ.pub, e₁) e₂ s₃
        (L₃.thread.strs (envThird E₁ E₂)) (L₃.wit k R.own (m₁.st.heard ++ m₂.st.heard ++ ds)) := by
  have t₁ := u₁.1
  have t₂ := u₂.1
  have i₁ : m₁.st.input = R.own := t₁.2.2.2.2.2.2.1
  have i₂ : m₂.st.input = R.common := hv₂ _ t₂.2.2.2.2.2.2
  have hx : m₁.st.input.x = ξ := by rw [i₁]; exact hξ
  have hp' : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).pubOf m₁.st.input.x =
      ξ.pub := by rw [hx]; exact hp₁
  have hs₁ : SameIn 0 n₁
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.strs E₁)
      (L₃.thread.strs (envThird E₁ E₂)) := by
    show SameIn 0 n₁ (Env.strs item (srcAt 0 n₁ n₂) E₁)
      (Env.strs L₃.item (srcAt 2 L₃.n₁ L₃.n₂) (envThird E₁ E₂))
    rw [hi₃, hn₃, hm₃]
    exact strs_first item n₁ n₂ E₁ E₂
  have hE : E₂.stored = E₁.stored := by
    funext i x
    have a := t₂.1.1 i x
    have b := t₁.1.1 i x
    rw [b, a, i₂, i₁]
    exact hst i x
  have hs₂ : SameIn n₁ (n₁ + n₂) (L₂.thread.strs E₂) (L₃.thread.strs (envThird E₁ E₂)) := by
    show SameIn n₁ (n₁ + n₂) (Env.strs L₂.item (srcAt 1 L₂.n₁ L₂.n₂) E₂)
      (Env.strs L₃.item (srcAt 2 L₃.n₁ L₃.n₂) (envThird E₁ E₂))
    rw [hi₃, hn₃, hm₃, hi₂, hn₂, hm₂]
    exact strs_shared item n₁ n₂ E₁ E₂ hE
  intro s₃ ds i hi
  simp only [startLast, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · have a := ProofFile.Honest.FirstThread.first_item_at_end _ (ξ := ξ) hp' t₁ oI (m₂.st.heard ++ ds)
    rw [i₁] at a
    have b := cI e₁ e₂ s₃ _ _ _ hs₁ a
    rwa [← List.append_assoc] at b
  · have a := ProofFile.Honest.FirstThread.first_item_at_end _ (ξ := ξ) hp' t₁ oV (m₂.st.heard ++ ds)
    rw [i₁] at a
    have b := cV e₁ e₂ s₃ _ _ _ hs₁ a
    rwa [← List.append_assoc] at b
  · have a := ProofFile.Honest.FirstThread.first_item_at_end _ (ξ := ξ) hp' t₁ oE (m₂.st.heard ++ ds)
    rw [i₁] at a
    have b := cE e₁ e₂ s₃ _ _ _ hAl hs₁ a
    rwa [← List.append_assoc] at b
  · exact hDot ds _
  · have a := ProofFile.Honest.FirstThread.shared_pin_at_end L₂ t₂ oO ds
    rw [i₂] at a
    have hlen : m₁.st.heard.length = L₃.near := by
      rw [hnear]
      exact drawsFit_length _ _ t₁.2.1
    have b := cO e₁ e₂ s₃ _ _ m₁.st.heard _ hlen hs₂ a
    rwa [← List.append_assoc] at b

end

/-- **THE PREMISE hItems OF door_heads_walk AT THE THREE TERMS**, with ends laid as there. -/
theorem items_at_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X₀ X' Wt₂ Wt₃ : Type} [Inhabited TS] [Inhabited Desc.K14.St]
    (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X')
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (N : NumbersS)
    (Mg₂ : Common W₀ Rc OnBytes.TableKey → MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt₂)
    (shape : Nat → Desc.K14.St → Bool) (nothingLeft : Desc.K14.St → Bool)
    (order₂ : Desc.K14.St → Prop)
    (wit₂ : Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Wt₂)
    (table₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
      Place × Table)
    (fixed₂ : Fmt.TreeSource → Nat) (Vd₂ : Common W₀ Rc OnBytes.TableKey → Prop)
    (Rd₂ : Nat → Common W₀ Rc OnBytes.TableKey → Desc.K14.St → Prop)
    (Kp₂ : Place → Desc.K14.St → Desc.K14.St → Prop)
    (Mg₃ : Local W₀ Rc ProofFile.Inst Tr → MeaningS Desc.K14.St (ProofFile.InstPub × TS) Wt₃)
    (ML : VerifiableInference.Desc.Last.MeaningL VerifiableInference.Desc.Third.S₃ Wt₃)
    (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St VerifiableInference.Desc.Third.S₃
      (ProofFile.InstPub × TS))
    (order₃ : VerifiableInference.Desc.Third.S₃ → Prop) (taken : List Fmt.TreeSource)
    (wit₃ : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt₃)
    (table₃ : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
    (fixed₃ : Fmt.TreeSource → Nat) (Vd₃ : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd₃ : Nat → Local W₀ Rc ProofFile.Inst Tr → VerifiableInference.Desc.Third.S₃ → Prop)
    (Kp₃ : Place → VerifiableInference.Desc.Third.S₃ → VerifiableInference.Desc.Third.S₃ → Prop)
    {m₀₁ : Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {m₀₂ : Coins Bk → Mid (Common W₀ Rc OnBytes.TableKey) X₀}
    {w₀ : W₀} {rc : Rc} {ξ : ProofFile.Inst} {k : Coins Bk}
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X'}
    {ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
      (ProofFile.InstPub × TS) × Desc.K14.St}
    (hR : ready (F0T OnBytes.secondHashFunction Zp Np cF) Bk H w₀ rc ξ k = .ok R)
    (tE : ends = fun k w hd =>
      ((w.x.pub,
        (endsBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread
          (SaidWalk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread BaseNil m₀₁)
          (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length
          (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
            fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread
          (SaidWalk (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂
            table₂ fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread BaseNil m₀₂)
          (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length id
          (fun w => ⟨w.w₀, w.rc, H.key w.x⟩) k w hd).1),
        (endsBy (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread
          (SaidWalk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread BaseNil m₀₁)
          (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length
          (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
            fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread
          (SaidWalk (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂
            table₂ fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread BaseNil m₀₂)
          (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length id
          (fun w => ⟨w.w₀, w.rc, H.key w.x⟩) k w hd).2))
    (ho₁ : ∀ b, b ≤ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread.opensAvailable b = true)
    (ho₂ : ∀ b, b ≤ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length →
      (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
        fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread.opensAvailable b = true)
    (hd₁ : ∀ k b, b ≤ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length → ∀ m,
      WalkedTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread m₀₁ k b m →
      DepthsAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread b k m)
    (hd₂ : ∀ k b, b ≤ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length → ∀ m,
      WalkedTo (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
        fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread m₀₂ k b m →
      DepthsAt (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
        fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread b k m)
    (five : ∀ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread
        (SaidWalk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread BaseNil m₀₁)
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
          fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread
        (SaidWalk (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
          fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread BaseNil m₀₂)
        (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k e₂ m₂ E₂ →
      ∀ s₃ ds, ∀ i ∈ VerifiableInference.Desc.Last.startLast,
        VerifiableInference.Desc.Last.ItemL.holds N (Mg₃ R.own) ML i (ξ.pub, e₁) e₂ s₃
          ((LastThread.lettersLast Zp Np cF H N Mg₃ ML PL order₃ taken ends wit₃ table₃ fixed₃
            item n₁ n₂ Vd₃ Rd₃ Kp₃ R.own).thread.strs (envThird E₁ E₂))
          (wit₃ k R.own (m₁.st.heard ++ m₂.st.heard ++ ds))) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread
        (SaidWalk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own).thread BaseNil m₀₁)
        (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
          fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread
        (SaidWalk (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂
          fixed₂ n₁ n₂ Vd₂ Rd₂ Kp₂ R.common).thread BaseNil m₀₂)
        (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.length k e₂ m₂ E₂ →
      (F0T OnBytes.secondHashFunction Zp Np cF).start₃ ξ.pub e₁ e₂ = .ok s₃ →
      (LastThread.lettersLast Zp Np cF H N Mg₃ ML PL order₃ taken ends wit₃ table₃ fixed₃
        item n₁ n₂ Vd₃ Rd₃ Kp₃ R.own).thread.Items
        ((LastThread.lettersLast Zp Np cF H N Mg₃ ML PL order₃ taken ends wit₃ table₃ fixed₃
          item n₁ n₂ Vd₃ Rd₃ Kp₃ R.own).thread.opened 0) k s₃ (R.start₃ H m₁ m₂)
        (envThird E₁ E₂) := by
  have hE := ProofFile.Honest.FirstThread.ends_at_door h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp N Mg₂
    shape nothingLeft order₂ wit₂ table₂ fixed₂ Vd₂ Rd₂ Kp₂ hR rfl rfl tE ho₁ ho₂ hd₁ hd₂
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ _
  exact ProofFile.Honest.FirstThread.items_at_door
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp R.own)
    (SharedThread.lettersShared Zp Np cF H N Mg₂ shape nothingLeft order₂ wit₂ table₂ fixed₂ n₁ n₂
      Vd₂ Rd₂ Kp₂ R.common)
    (LastThread.lettersLast Zp Np cF H N Mg₃ ML PL order₃ taken ends wit₃ table₃ fixed₃ item n₁ n₂
      Vd₃ Rd₃ Kp₃ R.own) (H := H) (ξ := ξ) (k := k) (R := R) rfl rfl rfl hE five
    e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂

end AtFullSide.K13

#print axioms AtFullSide.K13.items_at_letters
#print axioms AtFullSide.K13.five_at_door
#print axioms AtFullSide.K13.dot_at_the_door
#print axioms AtFullSide.K13.g_at_door
#print axioms AtFullSide.K13.point_at_door
