-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/HonestEntry.lean: THE COMPILED PROVER's PROOF STRING OF THE ENTRY's FILE IS
PRINTABLE (PrintableL, Johnson/Prover/Print/Entry.lean), at coins of the bytes' form, at that file's
own wire record (wqW, Johnson/RunOne/StrictLinkW.lean), under every family of oracle functions. The
twin of OnBytes/Prover/Print/Honest.lean's printable_of_prove, over its general lemmas.

Main names.
  quiet_wiresSL, sumJ_wiresSL, sum0_wiresSL   the wire record of a stretch of local rounds: a
    component that is not sent has no depth; as many depths as the data hold trees.
  printableL_of_prove   THE END.

What it asks. The prover has returned (π, τ) at the coins coinsOf (ds.length + 1) (ds.length + 1)
s.logLeaves bc: so every round's run value is bc.run1; the byte coins' lengths at a binding shape of
depth 0 (so the place is 0); the configuration's digest has 32 bytes; at most two trees a round; at
the outer places that are read: the kept leaf's salt begins with the configuration's digest, and the
symbol names its place.

Does not show: that any premise is met. Nothing on nonces or lengths in bytes (SizesL). Nothing on
acceptance, soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.EntryAtFull
import OnBytes.Prover.Print.Honest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open Rom
open _root_.Run (bytesToBits bitsToBytes leafSalt bitsToBytes_bytesToBits)
open _root_.Compile (Tag Opening)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run
open TypedOracleCompiler.Joined (sumJ sum0 FewJ Few0)
open _root_.Run.PQ (View SgX CK XO weX)
open OnBytes.Flat (linkSkeletonOfRoundData)
open Johnson.RunOne.StrictW (wqW)
open OnBytes.Prover OnBytes.Prover.Print

section Wire
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem quiet_wiresSL : ∀ ds : List PQ.RD,
    Quiet (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds)
  | [] => trivial
  | d :: ds =>
    ⟨fun _ => rfl, fun hn => by
      have e : d.trees = [] := trees_nil d.trees fun p => Bool.noConfusion (hn.1 p)
      show d.trees.map (·.a) = []
      rw [e]
      rfl, quiet_wiresSL ds⟩

theorem sumJ_wiresSL : ∀ ds : List PQ.RD,
    sumJ (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds) =
      (ds.map (·.trees.length)).sum
  | [] => rfl
  | d :: ds => by
    show (d.trees.map (·.a)).length + sumJ (PQ.uL C ds) _ (PQ.wiresSL C K chal ds) = _
    rw [sumJ_wiresSL ds, List.length_map, List.map_cons, List.sum_cons]

theorem sum0_wiresSL : ∀ ds : List PQ.RD,
    sum0 (PQ.uL C ds) (_root_.Run.Twin.allLo (PQ.SL C ds)) (PQ.wiresSL C K chal ds) = 0
  | [] => rfl
  | _ :: ds => by
    show 0 + sum0 (PQ.uL C ds) _ (PQ.wiresSL C K chal ds) = 0
    rw [sum0_wiresSL ds]

end Wire

section End
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {Y : Type} (dec : Y → View → Bool)
  {I X : Type} (L : BatchProtocolWithLeafBody I X) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (t : Tag)
  (embS : (p : OPos (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape) →
    OSym (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape p → Body L)
  (embP : PlainPart (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann →
    PlainPart (shapeOf L t) (annOf L t))
  (xin : Y → Option X) (cms : List (Dig 256)) (x : Y)
  (y : (twoExternalStrings (2 ^ a) SgX).Str) (xt : ℕ → TreeK 256 L)
  (σ : Strat (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape Unit) (bc : ByteCoins L)
  (cap : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (K + 1) L)) (cfg : ByteArray) (salt : ℕ)
  (s : OnBytes.Params.LinBindingShape) (π : OneProtocolProof 256 (linkSkeletonOfRoundData C ds a xs dec).up)
  (τ : Tr (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)

/-- **THE COMPILED PROVER's STRING OF THE ENTRY's FILE IS PRINTABLE.** -/
theorem printableL_of_prove
    (hp : (proveX t (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) embS embP xin cms x y xt σ
      (coinsOf (ds.length + 1) (ds.length + 1) s.logLeaves bc) cap).det g = .ok (π, τ))
    (hfit : bc.Fit salt s) (hs : s.logLeaves = 0) (hcfg : cfg.size = 32)
    (hd : ∀ d ∈ ds, d.trees.length ≤ 2)
    (hext : ∀ p ∈ (linkSkeletonOfRoundData C ds a xs dec).up.loc.extReads x τ.rho,
      SaltFrom cfg ((xt ((weX a).which p)).inp ((weX a).leaf p)).salt ∧
        ((twoExternalStrings (2 ^ a) SgX).rd y p).1 = p.elim (·.val) (·.val)) :
    PrintableL C ds a xs dec cfg π := by
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t _ _ embS embP xin cms x y xt σ _ cap g π τ).1 hp
  have hco := fit_coinsOf bc (ds.length + 1) (ds.length + 1) salt s hfit
  have hA : (linkSkeletonOfRoundData C ds a xs dec).up.ann = RoundSplits.allLocal (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape :=
    _root_.Run.Twin.allLo_eq _
  have hF : (linkSkeletonOfRoundData C ds a xs dec).up.ann.Fmt := by
    rw [hA]
    exact RoundSplits.fmt_allLocal _
  obtain ⟨R, hc⟩ := chain_at g (256 + 8 * salt) t cms (xin x) _ cap hco.leaf _ _ _ embS embP 0
    .first σ z hz hF (fewJ_wqW C ds a xs dec K chal hd) (few0_wqW C ds a xs dec K chal)
    (z.2.2.2.getD fun _ => false) (fun r hr => by rw [hr]; rfl)
  obtain ⟨hsl, hrq⟩ := chain_unjoined g t cms (xin x) _ cap _ _ _ embS embP 0 .first σ z hz rfl
    (by rw [hA]; exact TypedOracleCompiler.Joined.anySh_allLocal _)
  have hS := saltsIn_opensK 0 _ _ (wqW C ds a xs dec K chal).sh z.2.1
    (haveI := (wqW C ds a xs dec K chal).decO
     fun p => decide (p ∈ (linkSkeletonOfRoundData C ds a xs dec).up.loc.reads x z.1 (trK _ z.2.1 z.1).plains))
    hc.salts
  have hrun1 : bitsToBytes (bytesToBits bc.run1) = bc.run1 := bitsToBytes_bytesToBits _
  have hE : ∀ p op, (finish (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) x y xt
      (coinsOf (ds.length + 1) (ds.length + 1) s.logLeaves bc) z).ext p = some op →
      SaltFrom cfg op.salt ∧ op.sym.1 = p.elim (·.val) (·.val) := fun p op e => by
    have e' : (if decide (p ∈ (linkSkeletonOfRoundData C ds a xs dec).up.loc.extReads x z.1) = true then
        some ((xt ((weX a).which p)).opening ((weX a).leaf p) ((twoExternalStrings (2 ^ a) SgX).rd y p))
        else none) = some op := e
    split at e'
    · rename_i hdd
      obtain rfl := Option.some.inj e'
      exact hext p (by rw [rho_trK]; exact of_decide_eq_true hdd)
    · cases e'
  exact
    { salt := hco.salt
      cfg32 := hcfg
      roots := by
        have := length_rootsK g _ _ _ _ embS z.2.1 R hc.rounds
          (show Quiet _ _ (wqW C ds a xs dec K chal).sh from
            ⟨fun _ => rfl, fun _ => rfl, quiet_wiresSL C K chal ds⟩)
        refine this.trans ?_
        show (0 + sumJ _ _ (PQ.wiresSL C K chal ds)) + (0 + sum0 _ _ (PQ.wiresSL C K chal ds)) = _
        rw [sumJ_wiresSL, sum0_wiresSL]
        omega
      own := fun q op e => by
        obtain ⟨j, b, k, l, h1, h2, hsj⟩ := saltsIn_at 1 _ _ hS.2 q op e
        rw [hsj]
        show SaltFrom (bitsToBytes (bytesToBits bc.run1)) (leafSalt (bc.runAt _ _ j) _)
        have hl : (_root_.Run.Twin.up (PQ.SL C ds)).length = ds.length := by
          clear * -
          induction ds with
          | nil => rfl
          | cons d ds ih => exact congrArg (· + 1) ih
        have hj : bc.runAt (ds.length + 1) (ds.length + 1) j = bc.run1 := by
          unfold ByteCoins.runAt
          rw [if_pos (by omega)]
        rw [hrun1, hj]
        exact saltFrom_leafSalt _ _ hfit.run1
      ext0 := fun q op e => hE (.inl q) op e
      ext1 := fun q op e => hE (.inr q) op e
      rtreq := by
        show z.2.2.2.getD (fun _ => false) = fun _ => false
        rw [hrq]
        rfl
      slot := by
        have := hfit.place
        rw [hs] at this
        show bc.place = 0
        omega
      path := by
        show (if z.2.2.1.slotVal.isSome then bc.slotPath else []) = []
        rw [hsl]
        rfl
      rsalt := by
        show (if z.2.2.1.slotVal.isSome then _ else []) = []
        rw [hsl]
        rfl }

end End

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.quiet_wiresSL
#print axioms Johnson.Prover.Print.sumJ_wiresSL
#print axioms Johnson.Prover.Print.sum0_wiresSL
#print axioms Johnson.Prover.Print.printableL_of_prove
