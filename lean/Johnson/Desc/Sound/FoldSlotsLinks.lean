-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FoldSlotsLinks.lean: the row `fold_slots` (Johnson/Desc/Sound/FoldSlots.lean)
WITH THE WIDEST PREMISE ON A SHARED BLOCK, and THE CARRIAGE OF A PROVED CLAUSE FOR A BATCH to a
block.
Definitions, statements written as `def … : Prop`, and their proofs.

Why. `FoldSlots` asks of each block of the shared chain the law in two parts (`Piece.LostBoth`): the
form for a kind whose block's lemma is proved outright. THE LIBRARY HAS PROVED CLAUSES FOR A BATCH
ALREADY, on typed rounds: the five shared links of the test on the table (`LdLinP.linkPt`, `linkU`,
`linkLoc`, `linkO`, `linkZeta`: Cb/Ld/LdLinBProofs.lean), each with its own count of what is paid
once and what N times. These are not to be proved anew: they are to be CARRIED.

What is said.
  `Piece.Pays N on on' R R' act`: what the rule really uses of a shared block: its own reduction,
    run once by the shared part, is knowledge sound INTO its promise, at its own errors and with its
    own extractor, for the vectors of at most N statements that have one acting part (the library's
    `IOR.KnowBInto` at `SameKey act`).
  `PaysLink`: then it is a link of the batch from the key made backwards to any key behind it.
  `PaysOfLostBoth`: the law in two parts gives it.
  `PiecePaysOfProved`: THE CARRIAGE: from a typed reduction Kp with the clause for a batch (`KnowJ`,
    at the vectors with one typed key, at the typed errors δ, WHATEVER δ COUNTS ONCE OR N TIMES),
    along a reading G of the written rounds that hangs on the acting part alone, with the block's
    errors bearing δ (`CarryS.Fits`): the sibling, for a batch, of `PieceOfProved` | `PieceGoodIn`.
  `FoldSlotsPays`: `FoldSlots` with `EachPays` in the place of `EachLostBoth`: the other seven
    premises and the conclusion to the letter.

Kin that is called: `pullBad`, `pullBad_clean`, `jWithin_pull` (OnBytes/TypedOracleCompiler/Joined/CarryJ.lean): the
library's own carriage of bad sets along a keyed reading (there to `backS`, the typed reduction read
on the written rounds; here to the block's own reduction).

Every "there is", walked. `PiecePaysOfProved`, the premise on the block's yes: the image τ'
(determined by G), what Kp puts out there (determined), and a witness w' of it: asked to exist, as
in `PieceOfProved`: it stands in no extractor. None else.

Limits. Rules. No reading with `Fits` is shown of any block. At a reading under which no transcript
has an image the premise on the block's yes says that the block refuses all. In `PiecePaysOfProved`
a statement behind the block that lies outside the promise counts as having every witness (the
library's `orOff`): so the premise asks that Kp's output relation bears that case too (the library's
links are stated at such relations: `Rels.cf`).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldSlotsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links shA pullBad pullBad_clean jWithin_pull)
open _root_.CompileK.Joined (KnowJ allKind_const)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed Tr)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-! ## 1 What the rule uses of a shared block -/

/-- **A shared block pays for N slots**: knowledge sound into its promise, at its own errors, for
the vectors of at most N statements with one acting part. -/
def Piece.Pays (p : Piece C F S Cl W) (N : ℕ) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act : BKey F S) : Prop :=
  p.ior.KnowBInto (shAn p.ior.shape) N (IOR.SameKey act.2) on on' R R' p.ext p.err

/-- Every block of a row does, at the acting part of the place in front of it. -/
def EachPays (N : ℕ) (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (act : ℕ → BKey F S) : ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l =>
    p.Pays N (on i) (on (i + 1)) (R i) (R (i + 1)) (act i) ∧ EachPays N on R act (i + 1) l

/-- Then it is a link of the batch, from the key made backwards to any key behind it. -/
def PaysLink : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act kB : BKey F S) (N : ℕ),
    p.Pays N on on' R R' act →
    (p.bk on on' R R').LinkSh N (kkAt (p.keyBack act kB)) (kkAt kB)

/-- The law in two parts gives it. -/
def PaysOfLostBoth : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (act : BKey F S) (N : ℕ),
    p.LostBoth N on on' R R' act → p.Pays N on on' R R' act

/-! ## 2 The carriage of a proved clause for a batch -/

/-- **From a proved clause for a batch, on typed rounds, to a block of the shared chain.** Kp: the
typed reduction. G: the reading of the block's written rounds, a function of the acting part. δ: the
typed errors; the block's bear them. rd: the typed statement that is read off the block's. keyp: the
typed key; g: it is a function of the acting part. The premise on the block's yes: from a statement
with `on`, where the block says yes at τ, the reading has an image τ' and Kp puts out y there; and
every witness behind the block (a statement outside the promise counts as having every witness)
gives a witness w' of y such that a witness in front of Kp, had by its extractor from w', gives the
block's extractor's value as a witness in front of the block. -/
def PiecePaysOfProved : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (act : BKey F S) (N : ℕ)
    (Xp Yp Wp Wq κp : Type) (Kp : Reduction Xp Yp) (G : act.1 → CarryS (uLT C p.ds) Kp.shape)
    (δ : Err Kp.shape) (rd : S × F.E.Str → Xp) (keyp : Xp → κp) (g : act.1 → κp)
    (on on' : S × F.E.Str → Prop) (onp : Xp → Prop) (R R' : S × F.E.Str → W → Prop)
    (RAp : Xp → Wp → Prop) (RBp : Yp → Wq → Prop) (ep : Xp → Tr Kp.shape → Wq → Wp),
    (∀ k, (G k).Fits δ p.err) → (∀ a, on a → onp (rd a)) → (∀ a, keyp (rd a) = g (act.2 a)) →
    (∀ a τ b, on a → p.ior.red.out a τ = some b →
      ∃ τ' y, (G (act.2 a)).tr τ = some τ' ∧ Kp.out (rd a) τ' = some y ∧
        ∀ w, Reduction.orOff on' R' b w → ∃ w', RBp y w' ∧
          (RAp (rd a) (ep (rd a) τ' w') → R a (p.ext a τ w))) →
    KnowJ Kp (shA Kp.shape) N (IOR.SameKey keyp) onp RAp RBp ep δ →
    p.Pays N on on' R R' act

/-! ## 3 The row, with the widest premise -/

/-- **`FoldSlots` with `EachPays` in the place of `EachLostBoth`.** -/
def FoldSlotsPays : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ W TF TJ T3 : Type) (tF : TF) (tJ : TJ)
    (t3 : T3) (F : FileDescription (X × Rec)) (T : ThreeAt C D all F X₁ X₂ W) (Q : PlacesAt D all F W)
    (okF : X × Rec → TF → Bool) (okJ : F.XiPub × F.S₁ → TJ → Bool)
    (ok3 : F.XiPub × F.S₁ × F.S₂ → T3 → Bool)
    (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT C D.ds₃) (N : ℕ)
    (s₂ : Rec → F.S₂),
    OfDesc F T → (atDesc F T).Fits →
    EachGood Q.on₁ Q.R₁ 0 ((atDesc F T).p₁ :: (atDesc F T).l₁) →
    EachPays N Q.on₂ Q.R₂ (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂) 0
      ((atDesc F T).p₂ :: (atDesc F T).l₂) →
    EachGood Q.on₃ Q.R₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃) →
    (atDesc F T).Glued Q →
    (∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) →
    (∀ x rec, F.start₂ (F.pub (x, rec)) = s₂ rec) →
    ∀ rec : Rec,
      ((((atDesc F T).row tF tJ t3 okF okJ ok3).links
        ((atDesc F T).snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).comap fun x : X => (x, rec)).KnowsJ N
        (fun a : (F.XiPub × F.S₁) × (EAll D all).Str => (F.start₂ a.1.1, a.2.1)) (fun _ => ())

/-! ## 4 The proofs -/

theorem paysLink : PaysLink := by
  intro S Cl W C F p on on' R R' act kB N h
  exact ⟨Iop.knowB_conseq _ _ _ _ _ _ p.ior _ N _ _ _ _ _ _ _ _ _ _ h
    (fun a ha j j' aj aj' hj hj' => congrArg Prod.fst (ha j j' aj aj' hj hj')) (fun _ h => h)
    (fun _ _ _ h => h) (fun _ _ h => h), admBack S Cl W C F p act kB N⟩

theorem paysOfLostBoth : PaysOfLostBoth := by
  rintro S Cl W C F p on on' R R' act N ⟨εK, εO, hle, lostK, lostO, hK, hO, hb⟩
  obtain ⟨bad, c, J⟩ := Iop.knowB_of_lost_both S S act.1 F.E F.E W W p.ior N act.2 lostK lostO on R
    (Reduction.orOff on' R') p.ext εK εO hK hO
    (fun a τ b w ha hk ho hout hw =>
      (hb a τ b ha hk ho hout).2 w (hw.elim id fun n => absurd (hb a τ b ha hk ho hout).1 n))
  exact ⟨bad, c, fun a ha => Iop.JWithin.mono N _ _ _ hle (J a ha)⟩

theorem piecePaysOfProved : PiecePaysOfProved := by
  rintro S Cl W C F p act N Xp Yp Wp Wq κp Kp G δ rd keyp g on on' onp R R' RAp RBp ep fits hon hkey
    hyes ⟨bad', c', J'⟩
  refine ⟨fun a => pullBad (G (act.2 a)) (bad' (rd a)), ?_, ?_⟩
  · intro a τ b w ha hτ hb hw
    obtain ⟨τ', y, h1, h2, h3⟩ := hyes a τ b ha hb
    obtain ⟨w', hw', hr⟩ := h3 w hw
    exact hr (c' (rd a) τ' y w' (hon a ha) (pullBad_clean _ _ τ τ' h1 hτ) h2 hw')
  · intro a ha
    by_cases hne : ∃ j aj, a j = some aj
    · obtain ⟨j₀, a₀, h₀⟩ := hne
      have hadm : IOR.SameKey keyp fun j => (a j).map rd := by
        intro j j' x x' hx hx'
        obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨aj', haj', rfl⟩ := Option.map_eq_some_iff.mp hx'
        rw [hkey, hkey, ha j j' aj aj' haj haj']
      have ih := jWithin_pull N (G (act.2 a₀)) δ p.err (fits _) _ (J' _ hadm)
      refine cast (congrArg (Iop.JWithin N _ (shA _) p.err) (funext fun j => ?_)) ih
      beta_reduce
      cases hj : a j with
      | none => rfl
      | some aj =>
        show some (false, pullBad (G (act.2 a₀)) (bad' (rd aj))) =
          some (false, pullBad (G (act.2 aj)) (bad' (rd aj)))
        rw [ha j j₀ aj a₀ hj h₀]
    · refine Iop.jWithin_of_same N _ p.err (Iop.BadFam.empty _) _ (Iop.BadFam.empty_within _ _)
        fun j q hq => ?_
      obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact absurd ⟨j, aj, haj⟩ hne

/-- The premise of `ChainLink` at the keys made backwards. -/
theorem keyed_back_pays (N : ℕ) (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop)
    (act : ℕ → BKey F S) (kZ : BKey F S) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ),
      EachPays N on R act i (p :: l) → Keyed N on R i p l (keysBack act kZ i (p :: l)) kZ
  | [], p, i, h => paysLink S Cl W C F p _ _ _ _ (act i) kZ N h.1
  | q :: l, p, i, h =>
    ⟨keysBack act kZ (i + 1) (q :: l), paysLink S Cl W C F p _ _ _ _ (act i) _ N h.1,
      keyed_back_pays N on R act kZ l q (i + 1) h.2⟩

theorem foldSlotsPays : FoldSlotsPays := by
  intro C D all X Rec X₁ X₂ W TF TJ T3 tF tJ t3 F T Q okF okJ ok3 h₁ h₂ h₃ N s₂ hO hF g₁ hL g₃ hG ho
    one rec
  obtain ⟨e1, e2, hb⟩ := liftedAtDesc C D all (X × Rec) X₁ X₂ W F T hO
  have hh := each_hands Prod.snd (fun (t : (F.XiPub × F.S₁) × F.S₂) (s : F.S₂) => (t.1, s)) e1 e2
    D.t₁ (atDesc F T).l₂ (atDesc F T).p₂ 0
    (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂) (fun k => by rw [Nat.zero_add]; rfl)
    hF.tiled₂ hb
    (fun q hq d hd => ho d (hF.data₂ ▸ mem_rowData (atDesc F T).p₂ (atDesc F T).l₂ q hq d hd))
  have hkk := keyed_back_pays N Q.on₂ Q.R₂ (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂)
    (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂
      (0 + ((atDesc F T).p₂ :: (atDesc F T).l₂).length)) (atDesc F T).l₂ (atDesc F T).p₂ 0 hL
  obtain ⟨gh, hgh⟩ := headOfActs _ F.Cl W C _
    (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂) 0
    ((atDesc F T).p₂ :: (atDesc F T).l₂) hh
  refine ⟨?_, ?_, ?_, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩
  · exact LinkJ.ofLocal (allKind_const (fun _ => rfl) _) N
      (fun a ha => file_know₁ tF tJ t3 (atDesc F T) Q okF okJ ok3 h₁ h₂ h₃ hF g₁ hG.glue₁
        ((a.1, rec), a.2) ha)
      (fun y => (s₂ rec, y)) fun a τ b hb' => by
        have k := firstKeyAtDesc C D all (X × Rec) X₁ X₂ W TF TJ T3 tF tJ t3 F T Q okF okJ ok3 h₁ h₂
          h₃ hO ((a.1, rec), a.2) τ b hb'
        rw [one] at k
        exact k
  · refine seamLink C D all (X × Rec) _ _ _ _ _ F.Cl W TF TJ T3 _ _ tF tJ t3 (atDesc F T) Q okF okJ
      ok3 h₁ h₂ h₃ N _ _ _ _ hF hkk hG.glue₂
      ⟨fun k => gh (k.1, k.2, fun _ _ => none), fun a => ?_⟩ ⟨fun _ _ => (), fun _ _ => rfl⟩
    rw [hgh]
    refine congrArg gh ?_
    show (F.start₂ a.1.1, a.2.1,
      fun j x => if D.t₁ ≤ j ∧ j < (atDesc F T).p₂.base then _ else none) = _
    refine congrArg (fun f => (F.start₂ a.1.1, a.2.1, f)) (funext fun j => funext fun x => ?_)
    rw [if_neg]
    rw [hF.base₂]
    omega
  · exact LinkJ.ofLocal (allKind_const (fun _ => rfl) _) N
      (file_know₃ tF tJ t3 (atDesc F T) Q okF okJ ok3 h₁ h₂ h₃ hF g₃ hG.ends) (fun _ => ())
      (fun _ _ _ _ => rfl)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.paysLink
#print axioms VerifiableInference.Desc.Sound.paysOfLostBoth
#print axioms VerifiableInference.Desc.Sound.piecePaysOfProved
#print axioms VerifiableInference.Desc.Sound.foldSlotsPays
