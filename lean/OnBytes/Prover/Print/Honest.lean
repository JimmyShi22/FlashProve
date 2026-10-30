-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Honest.lean: THE COMPILED PROVER's PROOF STRING OF A WHOLE FILE IS PRINTABLE
(Printable, OnBytes/Prover/Print/Carrier.lean), at coins of the bytes' form (coinsOf,
OnBytes/Prover/Print/Coins.lean), at the file's own wire record (wqWhole, OnBytes/Maker/Wire.lean),
under every family of oracle functions.

Main names.
  fit_coinsOf          coins of the bytes' form have the lengths that the prover's theorem asks
    (Coins.Fit, OnBytes/Prover/Inv.lean) at 256 + 8 * salt and 256 bits.
  saltFrom_leafSalt    a run value of 32 bytes, then a salt's bytes: SaltFrom.
  SaltsIn              of a family of openings: each one's typed salt is the coins' at its round's
    number. saltsIn_opensK, saltsIn_L, saltsIn_R, saltsIn_at: the prover's openings are so; a cut
    of such a family is so; the round's number lies in the cut.
  Quiet, length_rootsK where a component that is not sent has no depth in the wire record, the
    prover's list of roots has as many members as the wire record has depths.
  quiet_whole, trees_whole   so it is at a whole file's wire record, and the number is treesIn D.
  printable_of_prove   THE END.

What it asks. The prover has returned (π, τ); the byte coins' lengths; at most maxRt trees in a
component (FewJ, Few0: two premises of the prover's own theorem yes_of_prove); the strategy has sent
the coins' run2 and run3 in the joining round's and the seam's plain parts, and the front's answers
again in the joining round; at the outer places that are read: the kept leaf's salt begins with the
configuration's digest, and the symbol names its place.

Does not show: that any premise is met: not that a strategy sends these plain parts, not that a
committer has salted the outer tree so. Nothing on words below the prime, nonces or lengths in bytes
(Canon, OnBytes/Prover/Print/Canon.lean). Nothing on acceptance, soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Carrier
import OnBytes.Prover.Print.Coins
import OnBytes.Prover.AtFile
import OnBytes.Maker.FitsLen
import OnBytes.Maker.WholeLaws
import OnBytes.Maker.TablesBack
import Run.CodingBitsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print

open _root_.Run _root_.Run.PQ Compile.Joined Rom
open _root_.Compile (Tag Opening)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃ opensL opensR sumJ sum0 FewJ Few0 WireSB.app)
open OnBytes.Maker OnBytes.Maker.Carrier
open OnBytes.Prover

/-! ## The coins' lengths -/

section Coins
variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

theorem size_runAt (bc : ByteCoins L) {salt : ℕ} {s : Params.LinBindingShape} (h : bc.Fit salt s)
    (nJ n3 i : ℕ) : (bc.runAt nJ n3 i).size = 32 := by
  unfold ByteCoins.runAt
  split
  · exact h.run1
  · split
    · exact h.run2
    · exact h.run3

/-- **The coins of the bytes' form have the lengths that the prover's theorem asks.** -/
theorem fit_coinsOf (bc : ByteCoins L) (nJ n3 salt : ℕ) (s : Params.LinBindingShape)
    (h : bc.Fit salt s) : (coinsOf nJ n3 s.logLeaves bc).Fit (256 + 8 * salt) 256 s.logLeaves where
  salt := by
    show (bytesToBits bc.run1).length = 256
    rw [length_bytesToBits, h.run1]
  leaf := fun i b k j => by
    show (leafSalt (bc.runAt nJ n3 i) (bc.leaf i b k j)).length = 256 + 8 * salt
    rw [length_leafSalt, size_runAt bc h, h.leaf]
  slot := h.place
  path := h.slotPath

theorem saltFrom_leafSalt (a b : ByteArray) (h : a.size = 32) : SaltFrom a (leafSalt a b) := by
  have hl : (bytesToBits a).length = 256 := by rw [length_bytesToBits, h]
  unfold SaltFrom leafSalt
  rw [List.take_left' hl, List.drop_left' hl]
  exact ⟨rfl, whole_bytesToBits b⟩

end Coins

/-! ## Whose salt an opening bears -/

section Salts
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- Each opening's typed salt is the coins' at its round's number; i: the first round's. -/
def SaltsIn (co : Coins lam L) :
    ℕ → (s : Shape) → ((p : OPos s) → Option (Opening lam (OSym s p))) → Prop
  | _, [], _ => True
  | i, _ :: s, f =>
    (∀ p op, f (.inl p) = some op → ∃ b k l, op.salt = co.leaf i b k l) ∧
      SaltsIn co (i + 1) s fun q => f (.inr q)

theorem saltsIn_opensK {co : Coins lam L} : ∀ (i : ℕ) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (kp : Kept lam L s) (rd : OPos s → Bool),
    SaltsAt co i s kp → SaltsIn co i s (opensK s A W kp rd)
  | _, [], _, _, _, _, _ => trivial
  | i, r :: s, (a, A), (w, W), (kp, ks), rd, h =>
    ⟨fun p op e => ⟨a.own p, w.tree p, w.place p,
        opensK_salt i (r :: s) (a, A) (w, W) (kp, ks) rd (.inl p) op h e⟩,
      saltsIn_opensK (i + 1) s A W ks (fun p => rd (.inr p)) h.2.2⟩

theorem saltsIn_L {co : Coins lam L} : ∀ {s u : Shape} (i : ℕ)
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
    SaltsIn co i (s ++ u) f → SaltsIn co i s (opensL f)
  | [], _, _, _, _ => trivial
  | _ :: _, _, i, f, h => ⟨h.1, saltsIn_L (i + 1) (fun q => f (.inr q)) h.2⟩

theorem saltsIn_R {co : Coins lam L} : ∀ {s u : Shape} (i : ℕ)
    (f : (p : OPos (s ++ u)) → Option (Opening lam (OSym (s ++ u) p))),
    SaltsIn co i (s ++ u) f → SaltsIn co (i + s.length) u (opensR (s := s) f)
  | [], _, _, _, h => h
  | _ :: s, _, i, f, h => by
    have := saltsIn_R (s := s) (i + 1) (fun q => f (.inr q)) h.2
    rw [List.length_cons, show i + (s.length + 1) = i + 1 + s.length by omega]
    exact this

theorem saltsIn_at {co : Coins lam L} : ∀ (i : ℕ) (s : Shape)
    (f : (p : OPos s) → Option (Opening lam (OSym s p))), SaltsIn co i s f →
    ∀ (p : OPos s) (op : Opening lam (OSym s p)), f p = some op →
      ∃ j b k l, i ≤ j ∧ j < i + s.length ∧ op.salt = co.leaf j b k l
  | _, [], _, _, p, _, _ => nomatch p
  | i, _ :: s, _, h, .inl p, op, e => by
    obtain ⟨b, k, l, hs⟩ := h.1 p op e
    exact ⟨i, b, k, l, le_refl i, by rw [List.length_cons]; omega, hs⟩
  | i, _ :: s, f, h, .inr q, op, e => by
    obtain ⟨j, b, k, l, h1, h2, hs⟩ := saltsIn_at (i + 1) s (fun q => f (.inr q)) h.2 q op e
    exact ⟨j, b, k, l, by omega, by rw [List.length_cons]; omega, hs⟩

/-! ## How many roots -/

/-- A component that is not sent has no depth in the wire record. -/
def Quiet : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (a, A), (w, W) =>
    (a.NoShared → w.depth0 = []) ∧ (a.NoSlot → w.depthJ = []) ∧ Quiet s A W

theorem length_rootsK (g : Fam (typedOracleFamily lam K L)) (sMT : ℕ) : ∀ (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L) (kp : Kept lam L s)
    (R : RootsOfChain lam s), RoundsAt g sMT s A W embS kp R → Quiet s A W →
    (rootsK s kp).length = sumJ s A W + sum0 s A W
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embS, (kp, ks), (rt, R), h, hq => by
    have h0 : kp.2.1.length = w.depth0.length := by
      rcases h.1 with ⟨_, e, hn⟩ | ⟨_, hc⟩
      · rw [e, hq.1 hn]
        rfl
      · exact hc.1
    have hJ : kp.2.2.length = w.depthJ.length := by
      rcases h.2.1 with ⟨_, e, hn⟩ | ⟨_, hc⟩
      · rw [e, hq.2.1 hn]
        rfl
      · exact hc.1
    have ih := length_rootsK g sMT s A W (fun p => embS (.inr p)) ks R h.2.2 hq.2.2
    show (kp.2.2.map TreeK.root ++ (kp.2.1.map TreeK.root ++ rootsK s ks)).length =
      (w.depthJ.length + sumJ s A W) + (w.depth0.length + sum0 s A W)
    rw [List.length_append, List.length_append, List.length_map, List.length_map, ih, h0, hJ]
    omega

theorem quiet_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B), Quiet s A W → Quiet u B V →
    Quiet (s ++ u) (RoundSplits.app A B) (WireSB.app W V)
  | [], _, _, _, _, _, _, h => h
  | _ :: _, _, (_, _), _, (_, W), V, h, h' => ⟨h.1, h.2.1, quiet_app W V h.2.2 h'⟩

theorem sumJ_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B),
    sumJ (s ++ u) (RoundSplits.app A B) (WireSB.app W V) = sumJ s A W + sumJ u B V
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, _), _, (w, W), V => by
    show w.depthJ.length + sumJ _ _ (WireSB.app W V) = w.depthJ.length + sumJ _ _ W + sumJ _ _ V
    rw [sumJ_app W V, Nat.add_assoc]

theorem sum0_app : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A)
    (V : RoundsQueryLayout lam K u B),
    sum0 (s ++ u) (RoundSplits.app A B) (WireSB.app W V) = sum0 s A W + sum0 u B V
  | [], _, _, _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (_, _), _, (w, W), V => by
    show w.depth0.length + sum0 _ _ (WireSB.app W V) = w.depth0.length + sum0 _ _ W + sum0 _ _ V
    rw [sum0_app W V, Nat.add_assoc]

end Salts

/-! ## At a whole file's wire record -/

theorem trees_nil : ∀ ts : List Fmt.Shape, (PosT ts → False) → ts = []
  | [], _ => rfl
  | _ :: _, h => (h (.inl ⟨0, Nat.two_pow_pos _⟩)).elim

section Wire
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem quiet_wiresLo : ∀ ds : List RDT,
    Quiet (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds)
  | [] => trivial
  | d :: ds =>
    ⟨fun _ => rfl, fun hn => by
      have e : d.trees = [] := trees_nil d.trees fun p => Bool.noConfusion (hn.1 p)
      show d.trees.map (·.a) = []
      rw [e]
      rfl, quiet_wiresLo ds⟩

theorem quiet_wiresSh : ∀ ds : List RDT,
    Quiet (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds)
  | [] => trivial
  | d :: ds =>
    ⟨fun hn => by
      have e : d.trees = [] := trees_nil d.trees fun p => Bool.noConfusion (hn.1 p)
      show d.trees.map (·.a) = []
      rw [e]
      rfl, fun _ => rfl, quiet_wiresSh ds⟩

theorem sum0_wiresLo : ∀ ds : List RDT,
    sum0 (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) = 0
  | [] => rfl
  | _ :: ds => by
    show 0 + sum0 (uLT C ds) _ (wiresLo C K chal ds) = 0
    rw [sum0_wiresLo ds]

theorem sumJ_wiresSh : ∀ ds : List RDT,
    sumJ (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) = 0
  | [] => rfl
  | _ :: ds => by
    show 0 + sumJ (uLT C ds) _ (wiresSh C K chal ds) = 0
    rw [sumJ_wiresSh ds]

variable (D : WholeD) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

theorem quiet_whole : Quiet (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
    (wqWhole C K chal D tF tJ t3 silent run).sh :=
  ⟨fun _ => rfl, fun _ => rfl, quiet_app _ _ (quiet_wiresLo C K chal D.ds₁)
    ⟨fun _ => rfl, fun _ => rfl, quiet_app _ _ (quiet_wiresSh C K chal D.ds₂)
      ⟨fun _ => rfl, fun _ => rfl, quiet_wiresLo C K chal D.ds₃⟩⟩⟩

theorem trees_whole :
    sumJ (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
        (wqWhole C K chal D tF tJ t3 silent run).sh +
      sum0 (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
        (wqWhole C K chal D tF tJ t3 silent run).sh = treesIn D := by
  have eJ : sumJ (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wqWhole C K chal D tF tJ t3 silent run).sh =
      (D.ds₁.map (·.trees.length)).sum + (D.ds₃.map (·.trees.length)).sum := by
    show 0 + sumJ _ _ (WireSB.app (wiresLo C K chal D.ds₁)
      (wiresOf C K chal D tF tJ t3).shJ) = _
    rw [sumJ_app, sumJ_wiresLo]
    show 0 + (_ + (0 + sumJ _ _ (WireSB.app (wiresSh C K chal D.ds₂)
      (wiresOf C K chal D tF tJ t3).sh₃))) = _
    rw [sumJ_app, sumJ_wiresSh]
    show 0 + (_ + (0 + (0 + (0 + sumJ _ _ (wiresLo C K chal D.ds₃))))) = _
    rw [sumJ_wiresLo]
    omega
  have e0 : sum0 (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wqWhole C K chal D tF tJ t3 silent run).sh = (D.ds₂.map (·.trees.length)).sum := by
    show 0 + sum0 _ _ (WireSB.app (wiresLo C K chal D.ds₁)
      (wiresOf C K chal D tF tJ t3).shJ) = _
    rw [sum0_app, sum0_wiresLo]
    show 0 + (0 + (0 + sum0 _ _ (WireSB.app (wiresSh C K chal D.ds₂)
      (wiresOf C K chal D tF tJ t3).sh₃))) = _
    rw [sum0_app, sum0_wiresSh]
    show 0 + (0 + (0 + (_ + (0 + sum0 _ _ (wiresLo C K chal D.ds₃))))) = _
    rw [sum0_wiresLo]
    omega
  rw [eJ, e0]
  unfold treesIn WholeD.t₁ WholeD.t₂
  omega

end Wire

/-! ## The end -/

section End
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List OnBytes.E) → JoinMsg (List OnBytes.E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool)
  {I X : Type} (L : BatchProtocolWithLeafBody I X) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (t : Tag)
  (embS : (p : OPos (wholeDesc C D tF tJ t3 silent run).batch.loc.shape) →
    OSym (wholeDesc C D tF tJ t3 silent run).batch.loc.shape p → Body L)
  (embP : PlainPart (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
    (wholeDesc C D tF tJ t3 silent run).batch.ann → PlainPart (shapeOf L t) (annOf L t))
  (xin : Xi → Option X) (cms : List (Dig 256)) (x : Xi)
  (y : (oneExternalString (2 ^ D.a) SgX).Str) (xt : ℕ → TreeK 256 L)
  (σ : Strat (wholeDesc C D tF tJ t3 silent run).batch.loc.shape Unit) (bc : ByteCoins L)
  (cap : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (K + 1) L)) (cfg : ByteArray) (salt : ℕ)
  (s : Params.LinBindingShape) (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
  (τ : Tr (wholeDesc C D tF tJ t3 silent run).batch.loc.shape)

/-- **THE COMPILED PROVER's STRING IS PRINTABLE.** -/
theorem printable_of_prove
    (hp : (proveX t (wholeDesc C D tF tJ t3 silent run).batch
      (wqWhole C K chal D tF tJ t3 silent run) embS embP xin cms x y xt σ
      (coinsOf (chainsOf C D tF tJ t3).nJ (chainsOf C D tF tJ t3).n3 s.logLeaves bc) cap).det g =
        .ok (π, τ))
    (hfit : bc.Fit salt s)
    (hJ : FewJ (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
      (wholeDesc C D tF tJ t3 silent run).batch.ann (wqWhole C K chal D tF tJ t3 silent run).sh)
    (h0 : Few0 (wholeDesc C D tF tJ t3 silent run).batch.loc.shape
      (wholeDesc C D tF tJ t3 silent run).batch.ann (wqWhole C K chal D tF tJ t3 silent run).sh)
    (hr2 : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.run = bc.run2)
    (hr3 : (pls₃ (wholeDesc C D tF tJ t3 silent run) π).1 = bc.run3)
    (hans : (pls₂ (wholeDesc C D tF tJ t3 silent run) π).1.answers =
      (pls₁ (wholeDesc C D tF tJ t3 silent run) π).1.answers)
    (hext : ∀ p ∈ (wholeDesc C D tF tJ t3 silent run).batch.loc.extReads x τ.rho,
      SaltFrom cfg ((xt ((weOne D.a).which p)).inp ((weOne D.a).leaf p)).salt ∧
        (y p).1 = p.val) :
    Printable C D tF tJ t3 silent run cfg s π := by
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t _ _ embS embP xin cms x y xt σ _ cap g π τ).1 hp
  have hco := fit_coinsOf bc (chainsOf C D tF tJ t3).nJ (chainsOf C D tF tJ t3).n3 salt s hfit
  have hL := chainsOf_laws C D tF tJ t3
  obtain ⟨R, hc⟩ := chain_at g (256 + 8 * salt) t cms (xin x) _ cap hco.leaf _ _ _ embS embP 0
    .first σ z hz ((chainsOf C D tF tJ t3).ann_fmt hL) hJ h0 (z.2.2.2.getD fun _ => false)
    (fun r hr => by rw [hr]; rfl)
  obtain ⟨hsl, -⟩ := chain_joined g t cms (xin x) _ cap _ _ _ embS embP 0 .first σ z hz rfl
    ((chainsOf C D tF tJ t3).anySh_ann hL)
  have hS := saltsIn_opensK 0 _ _ (wqWhole C K chal D tF tJ t3 silent run).sh z.2.1
    (haveI := (wqWhole C K chal D tF tJ t3 silent run).decO
     fun p => decide (p ∈ (wholeDesc C D tF tJ t3 silent run).batch.loc.reads x z.1
      (trK _ z.2.1 z.1).plains)) hc.salts
  have hrun1 : bitsToBytes (bytesToBits bc.run1) = bc.run1 := bitsToBytes_bytesToBits _
  rw [rho_trK] at hext
  exact
    { salt := hco.salt
      run2 := by rw [hr2]; exact hfit.run2
      run3 := by rw [hr3]; exact hfit.run3
      answers := hans
      roots := by
        have := length_rootsK g _ _ _ _ embS z.2.1 R hc.rounds
          (quiet_whole C K chal D tF tJ t3 silent run)
        rw [trees_whole] at this
        exact this
      own₁ := fun q op e => by
        obtain ⟨j, b, k, l, h1, h2, hs⟩ := saltsIn_at 1 _ _
          (saltsIn_L (s := (chainsOf C D tF tJ t3).c₁)
            (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) 0 _ hS).2 q op e
        rw [hs]
        show SaltFrom (bitsToBytes (bytesToBits bc.run1)) (leafSalt (bc.runAt _ _ j) _)
        have hj : bc.runAt (chainsOf C D tF tJ t3).nJ (chainsOf C D tF tJ t3).n3 j = bc.run1 := by
          unfold ByteCoins.runAt Chains.nJ
          rw [if_pos (by omega)]
        rw [hrun1, hj]
        exact saltFrom_leafSalt _ _ hfit.run1
      own₂ := fun q op e => by
        obtain ⟨j, b, k, l, h1, h2, hs⟩ := saltsIn_at _ _ _
          (saltsIn_L (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃) _ _
            (saltsIn_R (s := (chainsOf C D tF tJ t3).c₁)
              (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) 0 _ hS)).2 q op e
        rw [hs, hr2]
        show SaltFrom bc.run2 (leafSalt (bc.runAt _ _ j) _)
        have hj : bc.runAt (chainsOf C D tF tJ t3).nJ (chainsOf C D tF tJ t3).n3 j = bc.run2 := by
          have e1 : (chainsOf C D tF tJ t3).c₁.length = (chainsOf C D tF tJ t3).s₁.length + 1 := rfl
          unfold ByteCoins.runAt Chains.nJ Chains.n3
          rw [if_neg (by omega), if_pos (by omega)]
        rw [hj]
        exact saltFrom_leafSalt _ _ hfit.run2
      own₃ := fun q op e => by
        obtain ⟨j, b, k, l, h1, h2, hs⟩ := saltsIn_at _ _ _
          (saltsIn_R (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃) _ _
            (saltsIn_R (s := (chainsOf C D tF tJ t3).c₁)
              (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) 0 _ hS)).2 q op e
        rw [hs, hr3]
        show SaltFrom bc.run3 (leafSalt (bc.runAt _ _ j) _)
        have hj : bc.runAt (chainsOf C D tF tJ t3).nJ (chainsOf C D tF tJ t3).n3 j = bc.run3 := by
          have e1 : (chainsOf C D tF tJ t3).c₁.length = (chainsOf C D tF tJ t3).s₁.length + 1 := rfl
          have e2 : (chainsOf C D tF tJ t3).c₂.length = (chainsOf C D tF tJ t3).s₂.length + 1 := rfl
          unfold ByteCoins.runAt Chains.nJ Chains.n3
          rw [if_neg (by omega), if_neg (by omega)]
        rw [hj]
        exact saltFrom_leafSalt _ _ hfit.run3
      ext := fun p op e => by
        have e' : (if decide (p ∈ (wholeDesc C D tF tJ t3 silent run).batch.loc.extReads x z.1) =
            true then
            some ((xt ((weOne D.a).which p)).opening ((weOne D.a).leaf p) (y p)) else none) =
            some op := e
        split at e'
        · rename_i hd
          obtain rfl := Option.some.inj e'
          exact hext p (of_decide_eq_true hd)
        · cases e'
      slot := hfit.place
      path := by
        show (if z.2.2.1.slotVal.isSome then bc.slotPath else []).length = s.logLeaves
        rw [hsl]
        exact hfit.slotPath
      rsalt := ⟨bc.slotSalt, hfit.slotSalt, by
        show (if z.2.2.1.slotVal.isSome then rsOf (2 ^ s.logLeaves + bc.place) bc.slotSalt
          else []) = _
        rw [hsl]
        rfl⟩ }

end End

end OnBytes.Prover.Print

#print axioms OnBytes.Prover.Print.size_runAt
#print axioms OnBytes.Prover.Print.fit_coinsOf
#print axioms OnBytes.Prover.Print.saltFrom_leafSalt
#print axioms OnBytes.Prover.Print.SaltsIn
#print axioms OnBytes.Prover.Print.saltsIn_opensK
#print axioms OnBytes.Prover.Print.saltsIn_L
#print axioms OnBytes.Prover.Print.saltsIn_R
#print axioms OnBytes.Prover.Print.saltsIn_at
#print axioms OnBytes.Prover.Print.Quiet
#print axioms OnBytes.Prover.Print.length_rootsK
#print axioms OnBytes.Prover.Print.quiet_app
#print axioms OnBytes.Prover.Print.sumJ_app
#print axioms OnBytes.Prover.Print.sum0_app
#print axioms OnBytes.Prover.Print.trees_nil
#print axioms OnBytes.Prover.Print.quiet_wiresLo
#print axioms OnBytes.Prover.Print.quiet_wiresSh
#print axioms OnBytes.Prover.Print.sum0_wiresLo
#print axioms OnBytes.Prover.Print.sumJ_wiresSh
#print axioms OnBytes.Prover.Print.quiet_whole
#print axioms OnBytes.Prover.Print.trees_whole
#print axioms OnBytes.Prover.Print.printable_of_prove
