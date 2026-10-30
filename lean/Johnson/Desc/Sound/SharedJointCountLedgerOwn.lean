-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountLedgerOwn.lean: THE ROW's LEDGER, SECOND PART: THE DEBTS TOGETHER ARE THE
ROW AS `SharedJointCountRowG` SAYS IT: each block's law AT ITS KIND's OWN ERRORS, not first
at the cap. Statements written as `def … : Prop`, and their proofs.

The first part (Johnson/Desc/Sound/SharedJointCountLedger.lean) raises each kind's plain law to the cap
and then calls the rule for the stretch behind "LIN point" (`sharedJoinPlain`), which
is said at the pieces' errors. The row is now said with each kind's own errors
in it. So here:
  `eachLawsBNOwn_plain`: `eachLawsBN_plain` (Johnson/Desc/Sound/SharedJoinPlain.lean), LINE BY
    LINE, WITH own k x IN THE PLACE OF x.err: each kind's plain law FOR ONE STATEMENT at its own errors
    + `EachRides` ⟹ the law for a batch at these same errors, at every number of slots. What makes
    that possible: `Reduction.leadsK_of_hands` holds at every list of
    errors. A GENERALISATION OF `eachLawsBN_plain`: at own := the pieces' errors it is that lemma,
    which can be had from this.
  `LedgerPaysOwn`: for any row f :: pt :: q :: r.
  `RowGOfLedger`: AT A DESCRIPTION: with the front block's two debts on the record and the base paid by
    make (`frontByMake`, Johnson/Desc/Sound/SharedJointCountFront.lean) from three facts on the
    description's text. THE PREMISES, COUNTED AT ITS TEXT: EIGHTEEN:
    by make, a fact on the text, or a test on data (10): 1 ≤ N · OfDesc · Fits · the shared rounds open
      no tree below t₁ · Ns.lo = t₁ · l₂ = pt :: q :: r · each piece's errors are the cap · the shared
      flat list's head · that head says "ok" with the record as it is · it declares no round;
    the table's (1): ExtNamed;
    (b) (1, a clause a block): EachOwnBelow 128 own;
    the front block's (2): the book-keeping's Bool at 0 gives that at 1 · FrontRides;
    "LIN point"'s (2): own 1 pt = δK pt + N · δO pt · LeadsB at just these two;
    the blocks behind (2, a clause a block): EachPlainShOwn · EachRides.

Every "there is", walked: none of its own.
Limits. RULES: THEY CLOSE NO ROW. Every debt is a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountRowG
import Johnson.Desc.Sound.SharedJointCountFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open VerifiableInference.Desc.Shared

section Table
variable {P₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (Ns : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece C Fr (P₁ × S₂) Cl Wt) (l : List (Piece C Fr (P₁ × S₂) Cl Wt))
  (e₀ : ℕ → ActV S₂ Fr → Wt → Wt)

/-- **The stretch behind "LIN point", at the kinds' own errors.** -/
theorem eachLawsBNOwn_plain (n : ℕ) (own : OwnErrs C Fr (P₁ × S₂) Cl Wt) :
    ∀ (m : List (Piece C Fr (P₁ × S₂) Cl Wt)) (k : ℕ), 2 ≤ k → EachHands (actQ Ns p l) k m →
      EachPlainShOwn Ns Mg Pm Oc split p l e₀ own k m → EachRides Ns Mg Pm Oc split p l e₀ k m →
      EachLawsBNOwn (keyE Ns p l) (onQ₂ Ns Pm Oc split p l)
        (stepE Ns Mg Pm Oc split p l fun k a _ w => e₀ k ((actQ Ns p l k).2 a) w) n own k m
  | [], _, _, _, _, _ => trivial
  | x :: m, k, hk, hh, hp, hr => by
    refine ⟨?_, fun a b _ hq => hq.1,
      eachLawsBNOwn_plain n own m (k + 1) (Nat.le_succ_of_le hk) hh.2 hp.2 hr.2⟩
    obtain ⟨G, hG⟩ := hh.1
    have h1 := Reduction.leadsK_of_hands x.ior.red (actQ Ns p l k).2 (actQ Ns p l (k + 1)).2 G hG
      (onQ₂ Ns Pm Oc split p l k) (stepV Ns Mg Pm split p l e₀ k) (own k x) hp.1
    have h2 := h1.beside_sure
      (fun a b => Oc b.1.1 (strsOf Fr b.2) ∧
        ∀ w, relOwn Ns Mg 2 b w → relOwn Ns Mg 2 a (e₀ k ((actQ Ns p l k).2 a) w)) hr.1
    refine (h2.conseq (fun _ h => h) fun a τ b _ _ hq => ?_).bothN n
    obtain ⟨⟨hprom, hsh⟩, hoc, hown⟩ := hq
    refine ⟨⟨hprom, hoc⟩, fun w hw => ?_⟩
    have hw2 : relOwn Ns Mg 2 b w := by
      have := hw.2
      rw [relOwn_behind Ns Mg (k + 1) (Nat.le_succ_of_le hk)] at this
      exact this
    refine ⟨hsh w hw.1, ?_⟩
    rw [relOwn_behind Ns Mg k hk]
    exact hown w hw2

end Table

/-- **THE DEBTS TOGETHER ARE EACH BLOCK's LAW AT ITS KIND's OWN ERRORS**: for any row
f :: pt :: q :: r of pieces. -/
def LedgerPaysOwn : Prop :=
  ∀ (P₁ S₂ Cl Wt : Type) (C : CK) (Fr : Frame) (Ns : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
    (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool) (n : ℕ)
    (f pt q : Piece C Fr (P₁ × S₂) Cl Wt) (r : List (Piece C Fr (P₁ × S₂) Cl Wt))
    (e₀ : ℕ → ActV S₂ Fr → Wt → Wt) (own : OwnErrs C Fr (P₁ × S₂) Cl Wt)
    (δK δO : Err (uLT C pt.ds)),
    Tiled q r →
    (∀ x ∈ q :: r, ∃ b₀ : Block S₂ Cl, x.b = b₀.lift Prod.snd fun t s => (t.1, s)) →
    (∀ x ∈ q :: r, ∀ d ∈ x.ds, ∀ j ∈ d.opens, Ns.lo ≤ j) →
    (∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) → pt.base = f.base →
    (∀ s, Pm.shape 0 s = true → Pm.shape 1 s = true) →
    FrontRides Ns Mg Pm Oc split f (pt :: q :: r) →
    (∀ a w, extOf Ns f (pt :: q :: r) e₀ 0 a w = w) →
    own 1 pt = Err.add δK (Err.times n δO) →
    pt.ior.red.LeadsB (keyAt Prod.snd Ns.lo f (pt :: q :: r) 1)
      (onQ₂ Ns Pm Oc split f (pt :: q :: r) 1)
      (stepAt Ns Mg Pm Oc split f (pt :: q :: r) (extOf Ns f (pt :: q :: r) e₀) 1) δK δO →
    EachPlainShOwn Ns Mg Pm Oc split f (pt :: q :: r) e₀ own 2 (q :: r) →
    EachRides Ns Mg Pm Oc split f (pt :: q :: r) e₀ 2 (q :: r) →
    EachLawsBNOwn (keyAt Prod.snd Ns.lo f (pt :: q :: r)) (onQ₂ Ns Pm Oc split f (pt :: q :: r))
      (stepAt Ns Mg Pm Oc split f (pt :: q :: r) (extOf Ns f (pt :: q :: r) e₀)) n own 0
      (f :: pt :: q :: r)

theorem ledgerPaysOwn : LedgerPaysOwn := by
  intro P₁ S₂ Cl Wt C Fr Ns Mg Pm Oc split n f pt q r e₀ own δK δO ht hb ho f1 f2 f4 f5 hx hown hB
    hp hr
  have h10 := eachLawsBNOwn_plain Ns Mg Pm Oc split f (pt :: q :: r) e₀ n own (q :: r) 2
    (Nat.le_refl 2)
    (each_hands Prod.snd (fun t s => (t.1, s)) (fun _ _ => rfl) (fun _ _ _ => rfl) Ns.lo r q 2
      (actQ Ns f (pt :: q :: r))
      (fun k => by
        show actAt Fr Prod.snd Ns.lo (hiAt (2 + k) f (pt :: q :: r)) = _
        rw [Nat.add_comm]
        rfl) ht hb ho) hp hr
  exact ⟨frontLeadsBN Ns Mg Pm Oc split f pt (q :: r) _ n (own 0 f) f1 f2 f4 hx f5,
    fun _ _ _ h => h.1, ⟨δK, δO, by rw [hown]; exact Err.le_refl _, hB⟩, fun _ _ _ h => h.1, h10⟩

/-- **AT A DESCRIPTION: THE DEBTS TOGETHER ARE THE ROW AS `SharedJointCountRowG` SAYS IT.** -/
def RowGOfLedger : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ Wt : Type) (F : FileDescription (X × Rec))
    (T : ThreeAt C D all F X₁ X₂ Wt) (Ns : NumbersS) (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) Wt)
    (Pm : PromMeaning F.S₂) (Oc : F.XiPub × F.S₁ → Strs → Prop) (split : Bool) (N : ℕ)
    (pt q : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)
    (r : List (Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt))
    (e₀ : ℕ → ActV F.S₂ (frameAt D all D.key₂ (atDesc F T).ft₂) → Wt → Wt)
    (same : Comp → Wt → Wt → Prop)
    (own : OwnErrs C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)
    (δK δO : (p : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl
      Wt) → Err (uLT C p.ds))
    (fb : Block F.S₂ F.Cl) (rest : List (Block F.S₂ F.Cl)),
    1 ≤ N →
    OfDesc F T → (atDesc F T).Fits → (∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) → Ns.lo = D.t₁ →
    (atDesc F T).l₂ = pt :: q :: r →
    EachCapped 128 ((atDesc F T).p₂ :: pt :: q :: r) →
    F.shared.blocksInOrder = fb :: rest → (∀ s rs gs, fb.decide s rs gs = .ok s) → fb.rounds = [] →
    ExtNamed split (extOf Ns (atDesc F T).p₂ (pt :: q :: r) e₀) same →
    EachOwnBelow 128 own 0 ((atDesc F T).p₂ :: pt :: q :: r) →
    (∀ s, Pm.shape 0 s = true → Pm.shape 1 s = true) →
    FrontRides Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: q :: r) →
    own 1 pt = Err.add (δK pt) (Err.times N (δO pt)) →
    pt.ior.red.LeadsB (keyAt Prod.snd Ns.lo (atDesc F T).p₂ (pt :: q :: r) 1)
      (onQ₂ Ns Pm Oc split (atDesc F T).p₂ (pt :: q :: r) 1)
      (stepAt Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: q :: r)
        (extOf Ns (atDesc F T).p₂ (pt :: q :: r) e₀) 1) (δK pt) (δO pt) →
    EachPlainShOwn Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: q :: r) e₀ own 2 (q :: r) →
    EachRides Ns Mg Pm Oc split (atDesc F T).p₂ (pt :: q :: r) e₀ 2 (q :: r) →
    SharedJointCountRowG C D all X Rec X₁ X₂ Wt F T Ns Mg Pm Oc split N
      (extOf Ns (atDesc F T).p₂ (atDesc F T).l₂ e₀) same own δK δO

theorem rowGOfLedger : RowGOfLedger := by
  intro C D all X Rec X₁ X₂ Wt F T Ns Mg Pm Oc split N pt q r e₀ same own δK δO fb rest hN hO hf
    opens hlo hl hc hfl hok hrd hx hbel f4 f5 hown hB hp hr
  obtain ⟨f1, f2⟩ := frontByMake C D all (X × Rec) X₁ X₂ Wt F T fb rest pt (q :: r) hO hf hfl hok
    hrd hl
  obtain ⟨-, -, hb⟩ := liftedAtDesc C D all (X × Rec) X₁ X₂ Wt F T hO
  have ht := hf.tiled₂
  have hd := hf.data₂
  rw [hl] at hb ht hd
  unfold SharedJointCountRowG
  rw [hl, ← hlo]
  refine ⟨hN, rfl, hc, hx, hbel, ?_, fun pt' h' => ?_⟩
  · exact ledgerPaysOwn _ _ _ _ C _ Ns Mg Pm Oc split N (atDesc F T).p₂ pt q r e₀ own (δK pt) (δO pt)
      ht.2.2.2.2.2.2.2.2
      (fun x hx' => hb x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx')))
      (fun x hx' d hd' j hj => hlo ▸ opens d
        (hd ▸ mem_rowData (atDesc F T).p₂ (pt :: q :: r) x
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx')) d hd') j hj)
      f1 f2 f4 f5 (fun a w => hx.1 0 (by cases split <;> rfl) a w) hown hB hp hr
  · obtain rfl : pt = pt' := by simpa using h'
    exact ⟨hown, hB⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.eachLawsBNOwn_plain
#print axioms VerifiableInference.Desc.Sound.ledgerPaysOwn
#print axioms VerifiableInference.Desc.Sound.rowGOfLedger
