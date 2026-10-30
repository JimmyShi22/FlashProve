-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/AcceptAtA.lean: the decision of a file's description says yes at the transcript that
the compiled verifier builds from the typed proof string of a file on which the verifier program has
said yes, if the verifier's messages give the draws that were read, but for the digests drawn
(OnBytes/Maker/ViewsAlike.lean).

Main definitions.
  `DrawsHeldA`: what is asked of the verifier's messages: stretch by stretch they give the draws
    that were read, but for the digests, and the proofs of work pass.
Main theorems.
  `holdsA_lo`, `holdsA_sh`, `holdsA_typeFile`: the compiled verifier's transcript at a value of the
    typing holds what was read.
  `accept_mkTrA`: the decision's yes at the transcript over the whole shape. `accept_threeA`: the
    same at the three chains' transcripts in a row: the field `accept` of `Cuts`
    (OnBytes/TypedOracleCompiler/Joined/YesByCuts.lean) and of `AfterRuns` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean).
  `accept_key_of_givesA`, `accept_proof_of_givesA`: the same from `PortGives`
    (OnBytes/Maker/OfThreeChains.lean) and the program's yes.

  `TrHeldA`, `fileHeldA_of`, `keyIORAt_of_givesA`, `proofIORAt_of_givesA`, `keyIOR_of_readA`,
    `proofIOR_of_readA`, `keyIOR_of_checkA`, `proofIOR_of_checkA`: the yes of `keyIOR` and of
    `proofIOR` (OnBytes/Maker/Files.lean) at a transcript τ, from the program's reading and yes, if
    the dry runs at the fixed record or instance state the rounds of the key read, the three tests
    pass at these rounds, the instance's key is the key read (for a proof file also: its block is
    the block read under, and has the law's relation), `TrHeldA` holds of τ (with it the draws and
    the proofs of work: shown of no transcript in this file), and the silent rounds' test says yes
    at τ. Johnson/Top/KeyTop.lean and ProofTop.lean call the last two. No other file calls
    `accept_key_of_givesA` or `accept_proof_of_givesA`.

What `accept_mkTrA` and `accept_threeA` ask: that the typing returns; of the roots with which the
transcript is built, that each component sent has as many roots as trees, and that the component of
each round's kind is sent (OnBytes/Maker/TypingFlags.lean pays both for what runs yield);
`DrawsHeldA`; `ReadFits` (OnBytes/Maker/AcceptAt.lean); that the silent rounds' test says yes at the
three plain parts given to the typing; that the run says yes at all views that are the file's own
three but for the digests drawn.

Nothing in `DrawsHeldA`, `HoldsA`, `FileHeldA` or `TrHeldA` ties the value of either seal, though
the program's reader uses both: that is left to whoever shows what the chains' values under g are.

What is not claimed. None of the hypotheses. `DrawsHeldA` is the matter of the hash chain: that it
is met at any oracle functions is shown by nothing here. Nothing on soundness.


-/
import OnBytes.Maker.PortAccept
import OnBytes.Maker.ViewsAlike

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open _root_.Run _root_.Run.PQ
open OnBytes.TwoLaws (LAlike DrawnAlike ViewAlike)
open OnBytes.Params (Rounds)

/-- **What is asked of the verifier's messages**: stretch by stretch they give the draws that were
read, but for the digests, and the proofs of work pass. -/
structure DrawsHeldA (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (r : Proof.TailRead) (ρ : Rho (chainsOf C D tF tJ t3).sh) : Prop where
  d₁ : LAlike DrawnAlike (r.first.out.rounds.toList.dropLast.map (·.drawn))
    (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ))
  d₂ : LAlike DrawnAlike (r.shared.out.rounds.toList.map (·.drawn))
    (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ))
  d₃ : LAlike DrawnAlike (r.second.out.rounds.toList.map (·.drawn))
    (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ))
  w₁ : passT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) = true
  w₂ : passT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ) = true
  w₃ : passT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ) = true

section Stretch
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (ds : List RDT) (base : ℕ)
  (tabs : List (ℕ × List (ℕ × Row3))) (ros : List Fmt.RoundOut) (R : RootsOfChain 256 (uLT C ds))
  (pl : Plains (uLT C ds)) (ρ : Rho (uLT C ds))

theorem holdsA_lo (h : SentLo C ds R) (hpl : plainsT C ds ros = some pl)
    (hd : LAlike DrawnAlike (ros.map (·.drawn)) (drawnT C ds ρ)) :
    HoldsA C ds base tabs ros (mkTr (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) R
      pl ρ (opensT C ds base tabs)) where
  plains := by rw [plains_lo C K chal ds R pl ρ _ h]; exact hpl
  drawn := by rw [mkTr_rho]; exact hd
  read := fun p op ho => read_lo C K chal ds R pl ρ _ p op h ho

theorem holdsA_sh (h : SentSh C ds R) (hpl : plainsT C ds ros = some pl)
    (hd : LAlike DrawnAlike (ros.map (·.drawn)) (drawnT C ds ρ)) :
    HoldsA C ds base tabs ros (mkTr (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds))
      (wiresSh C K chal ds) R pl ρ (opensT C ds base tabs)) where
  plains := by rw [plains_sh C K chal ds R pl ρ _ h]; exact hpl
  drawn := by rw [mkTr_rho]; exact hd
  read := fun p op ho => read_sh C K chal ds R pl ρ _ p op h ho

end Stretch

section File
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (W : Three.Whole)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **At a value of the typing**: the tables, which two equations fix, the three records `HoldsA`
and the stored string's columns. -/
theorem holdsA_typeFile (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π)
    (R : RootsOfChain 256 (chainsOf C (WholeD.of a W) tF tJ t3).sh) (ρ : Rho (chainsOf C (WholeD.of a W) tF tJ
                t3).sh)
    (hF : RtFlagsAll (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ
      t3).ann (wiresOf C K chal (WholeD.of a W) tF tJ t3).sh R)
    (hK : SentK (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann
      R)
    (hρ : DrawsHeldA C (WholeD.of a W) tF tJ t3 r ρ) :
    ∃ tabs etab, tabsWFull W sb r = some tabs ∧ extTabWFull a cfg W r = some etab ∧
      TabsHold W sb r tabs ∧ ExtHolds a W r etab ∧
      HoldsA C (WholeD.of a W).ds₁ 0 tabs r.first.out.rounds.toList.dropLast
        ((chainsOf C (WholeD.of a W) tF tJ t3).tr₁ (mkTr (chainsOf C (WholeD.of a W) tF tJ t3).sh
          (chainsOf C (WholeD.of a W) tF tJ t3).ann
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens)) ∧
      HoldsA C (WholeD.of a W).ds₂ (WholeD.of a W).t₁ tabs r.shared.out.rounds.toList
        ((chainsOf C (WholeD.of a W) tF tJ t3).tr₂ (mkTr (chainsOf C (WholeD.of a W) tF tJ t3).sh
          (chainsOf C (WholeD.of a W) tF tJ t3).ann
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens)) ∧
      HoldsA C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂) tabs
        r.second.out.rounds.toList
        ((chainsOf C (WholeD.of a W) tF tJ t3).tr₃ (mkTr (chainsOf C (WholeD.of a W) tF tJ t3).sh
          (chainsOf C (WholeD.of a W) tF tJ t3).ann
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens)) ∧
      ∀ (x : ℕ) (hx : x < 2 ^ a) c s pt, etab.lookup x = some (c, s, pt) →
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext.build
          (fun p => (π.ext p).map Opening.sym) ⟨x, hx⟩ = (x, c) := by
  obtain ⟨tabs, ext, ht, he, h'⟩ :=
    typeFile_some C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h
  obtain ⟨etab, hE, rfl⟩ := Option.map_eq_some_iff.1 he
  obtain ⟨pl₁, pl₂, pl₃, h1, h2, h3, hp, ho⟩ := toBPrfW_parts C (WholeD.of a W) tF tJ t3 pF pJ p3
    tabs silent run _ salt path r π h'
  obtain ⟨s1, s2, s3⟩ := sent_of_flags C K chal (WholeD.of a W) tF tJ t3 R hF hK
  refine ⟨tabs, etab, ht, hE, tabsWFull_holds ht, extTabWFull_holds hE, ?_, ?_, ?_, ?_⟩
  · rw [hp, ho]
    exact (tr₁_typed C (WholeD.of a W) tF tJ t3 pF pJ p3 pl₁ pl₂ pl₃ tabs _ _ _ K chal R ρ) ▸
      holdsA_lo C K chal (WholeD.of a W).ds₁ 0 tabs _ _ pl₁ _ s1 h1 hρ.d₁
  · rw [hp, ho]
    exact (tr₂_typed C (WholeD.of a W) tF tJ t3 pF pJ p3 pl₁ pl₂ pl₃ tabs _ _ _ K chal R ρ) ▸
      holdsA_sh C K chal (WholeD.of a W).ds₂ (WholeD.of a W).t₁ tabs _ _ pl₂ _ s2 h2 hρ.d₂
  · rw [hp, ho]
    exact (tr₃_typed C (WholeD.of a W) tF tJ t3 pF pJ p3 pl₁ pl₂ pl₃ tabs _ _ _ K chal R ρ) ▸
      holdsA_lo C K chal (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂) tabs _ _ pl₃
        _ s3 h3 hρ.d₃
  · intro x hx c s pt hl
    rw [toBPrfW_ext C (WholeD.of a W) tF tJ t3 silent run pF pJ p3 tabs _ salt path r π h']
    exact build_atT a etab x hx c s pt hl

/-- **The decision says yes at the transcript that the compiled verifier builds from a value of the
typing.** -/
theorem accept_mkTrA (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π)
    (R : RootsOfChain 256 (chainsOf C (WholeD.of a W) tF tJ t3).sh) (ρ : Rho (chainsOf C (WholeD.of a W) tF tJ
                t3).sh)
    (hF : RtFlagsAll (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ
      t3).ann (wiresOf C K chal (WholeD.of a W) tF tJ t3).sh R)
    (hK : SentK (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann
      R)
    (hρ : DrawsHeldA C (WholeD.of a W) tF tJ t3 r ρ) {S₁ S₂ S₃ : Fmt.SpecX}
    (hr : ReadFits a W r S₁ S₂ S₃) (x : Xi) (hsil : silent x pF pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → run x v₁ v₂ v₃ = true) :
    (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).accept x
      ((wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext.build
        fun p => (π.ext p).map Opening.sym)
      (mkTr (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann
        (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens) = true := by
  obtain ⟨tabs, etab, -, -, hT, hE, H₁, H₂, H₃, hy⟩ := holdsA_typeFile C K chal a W tF tJ t3 silent
    run sb
    cfg pF pJ p3 salt path r π h R ρ hF hK hρ
  obtain ⟨tabs', ext', -, -, h'⟩ :=
    typeFile_some C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h
  obtain ⟨pl₁, pl₂, pl₃, -, -, -, hpl, -⟩ := toBPrfW_parts C (WholeD.of a W) tF tJ t3 pF pJ p3 tabs'
    silent run ext' salt path r π h'
  have q₁ := (rhoT_eq C _ ((chainsOf C (WholeD.of a W) tF tJ t3).tr₁ (mkTr _ _
    (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens))).trans
    (((chainsOf C (WholeD.of a W) tF tJ t3).rho_tr₁ _).trans (congrArg _ (mkTr_rho _ _ _ R π.plains
      ρ π.opens)))
  have q₂ := (rhoT_eq C _ ((chainsOf C (WholeD.of a W) tF tJ t3).tr₂ (mkTr _ _
    (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens))).trans
    (((chainsOf C (WholeD.of a W) tF tJ t3).rho_tr₂ _).trans (congrArg _ (mkTr_rho _ _ _ R π.plains
      ρ π.opens)))
  have q₃ := (rhoT_eq C _ ((chainsOf C (WholeD.of a W) tF tJ t3).tr₃ (mkTr _ _
    (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens))).trans
    (((chainsOf C (WholeD.of a W) tF tJ t3).rho_tr₃ _).trans (congrArg _ (mkTr_rho _ _ _ R π.plains
      ρ π.opens)))
  have sF := msgF_mkTr (wiresOf C K chal (WholeD.of a W) tF tJ t3) R π.plains ρ π.opens hK
  have sJ := msgJ_mkTr (wiresOf C K chal (WholeD.of a W) tF tJ t3) R π.plains ρ π.opens rfl hK
  have s3 := msg3_mkTr (wiresOf C K chal (WholeD.of a W) tF tJ t3) R π.plains ρ π.opens hK
  rw [hpl, plAF] at sF
  rw [hpl, plAJ1] at sJ
  rw [hpl, plA31] at s3
  have out := whole_yesA C a W tF tJ t3 silent run x _ _
    (⟨hT, hE, hr.shape, hr.bare, hr.st₁, hr.st₂, hr.st₃, hr.ft₁, hr.ft₂, hr.ft₃, hr.ls₁, hr.ls₂,
      hr.ls₃, H₁, H₂, H₃, hy, hr.v₁, hr.v₂, hr.v₃, hr.pw₁, hr.pw₂, hr.pw₃,
      q₁.symm ▸ hρ.w₁, q₂.symm ▸ hρ.w₂, q₃.symm ▸ hρ.w₃⟩ :
      FileHeldA C a W sb r tabs etab S₁ S₂ S₃ _ _ _ _)
    (by
      rw [← hpl] at sF sJ s3
      have tF' : ((chainsOf C (WholeD.of a W) tF tJ t3).msgF (mkTr _ _
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens)).2 = pF :=
        sF
      have tJ' : ((chainsOf C (WholeD.of a W) tF tJ t3).msgJ (mkTr _ _
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens)).2 = pJ :=
        sJ
      have t3' : ((chainsOf C (WholeD.of a W) tF tJ t3).msg3 (mkTr _ _
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).sh R π.plains ρ π.opens)).2 = p3 :=
        s3
      rw [tF', tJ', t3']
      exact hsil) hrun
  show ((reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).out x _ _).isSome = true
  rw [out]
  rfl

/-- **The decision says yes at the three chains' transcripts in a row.** -/
theorem accept_threeA (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
    (path : List ByteArray) (r : Proof.TailRead)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (h : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π)
    (A : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁) (B : Out 256 (chainsOf C (WholeD.of a W)
      tF tJ t3).c₂) (E : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (hF : RtFlagsAll (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ
      t3).ann (wiresOf C K chal (WholeD.of a W) tF tJ t3).sh
      (glue A B E).2.1)
    (hK : SentK (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann
      (glue A B E).2.1)
    (hρ : DrawsHeldA C (WholeD.of a W) tF tJ t3 r (glue A B E).1) {S₁ S₂ S₃ : Fmt.SpecX}
    (hr : ReadFits a W r S₁ S₂ S₃) (x : Xi) (hsil : silent x pF pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → run x v₁ v₂ v₃ = true) :
    (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).accept x
      ((wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run).ext.build
        fun p => (π.ext p).map Opening.sym)
      (Tr.app (s := (chainsOf C (WholeD.of a W) tF tJ t3).c₁) (t := (chainsOf C (WholeD.of a W) tF
        tJ t3).c₂ ++ (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
        (TypedOracleCompiler.Joined.tr₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) π A)
        (Tr.app (s := (chainsOf C (WholeD.of a W) tF tJ t3).c₂) (t := (chainsOf C (WholeD.of a W) tF
          tJ t3).c₃)
          (TypedOracleCompiler.Joined.tr₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) π B)
          (TypedOracleCompiler.Joined.tr₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) π E))) = true := by
  rw [three_eq_mkTr]
  exact accept_mkTrA C K chal a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r π h _ _ hF hK hρ
    hr x hsil hrun

end File

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) {TF TJ T3 : Type}
  (tF : TF) (tJ : TJ) (t3 : T3) {r : Proof.TailRead} {S₁ S₂ S₃ : Fmt.SpecX}
  {Rs : Rounds × Rounds × Rounds}

/-- **A key file.** -/
theorem accept_key_of_givesA {R : Type} (W : Three.Whole)
    (hW : W = Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) (G : PortGives a Rs r S₁ S₂ S₃) (ok : Bool)
    (hok : ok = true) (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (table : Params.TableName) (hyes : Key.keyRefusal k table r = none)
    (x : R) (hkey : key x = r.key) (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt :
      ByteArray)
    (path : List ByteArray)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k)).batch)
    (ht : typeFile C a W tF tJ t3 silent (keyRun W ok key k) sb cfg pF pJ p3 salt path r = some π)
    (A : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁) (B : Out 256 (chainsOf C (WholeD.of a W)
      tF tJ t3).c₂) (E : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (hF : RtFlagsAll (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ
      t3).ann (wiresOf C K chal (WholeD.of a W) tF tJ t3).sh
      (glue A B E).2.1)
    (hK : SentK (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann
      (glue A B E).2.1)
    (hρ : DrawsHeldA C (WholeD.of a W) tF tJ t3 r (glue A B E).1)
    (hsil : silent x pF pJ p3 = true) :
    (wholeDesc C (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k)).accept x
      ((wqWhole C K chal (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k)).ext.build
        fun p => (π.ext p).map Opening.sym)
      (Tr.app (s := (chainsOf C (WholeD.of a W) tF tJ t3).c₁) (t := (chainsOf C (WholeD.of a W) tF
        tJ t3).c₂ ++ (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
        (TypedOracleCompiler.Joined.tr₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k))
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k)) π A)
        (Tr.app (s := (chainsOf C (WholeD.of a W) tF tJ t3).c₂) (t := (chainsOf C (WholeD.of a W) tF
          tJ t3).c₃)
          (TypedOracleCompiler.Joined.tr₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k))
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k)) π B)
          (TypedOracleCompiler.Joined.tr₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k))
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent (keyRun W ok key k)) π E))) = true :=
              by
  subst hW
  exact accept_threeA C K chal a _ tF tJ t3 silent _ sb cfg pF pJ p3 salt path r π ht A B E hF hK
    hρ G.fits x hsil (keyRun_yesA _ ok key k table r x hok hkey G.roots G.sealed G.okWords hyes)

/-- **A proof file.** -/
theorem accept_proof_of_givesA {X R : Type} (W : Three.Whole)
    (hW : W = Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) (G : PortGives a Rs r S₁ S₂ S₃) (ok : Bool)
    (hok : ok = true) (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (table : Params.TableName)
    (x : X × R) (hyes : Proof.proofRefusal c table (block x.1) r = none)
    (hb : TwoLaws.Carries (TwoLaws.Alike TwoLaws.AnyGiven false)
      (TwoLaws.FirstEndAlike TwoLaws.AnyGiven) (block x.1) (block x.1))
    (hkey : key x.2 = r.key) (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt :
      ByteArray)
    (path : List ByteArray)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block)).batch)
    (ht : typeFile C a W tF tJ t3 silent (proofRun W ok key c block) sb cfg pF pJ p3 salt path r =
      some π)
    (A : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁) (B : Out 256 (chainsOf C (WholeD.of a W)
      tF tJ t3).c₂) (E : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (hF : RtFlagsAll (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ
      t3).ann (wiresOf C K chal (WholeD.of a W) tF tJ t3).sh
      (glue A B E).2.1)
    (hK : SentK (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann
      (glue A B E).2.1)
    (hρ : DrawsHeldA C (WholeD.of a W) tF tJ t3 r (glue A B E).1)
    (hsil : silent x pF pJ p3 = true) :
    (wholeDesc C (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block)).accept x
      ((wqWhole C K chal (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block)).ext.build
        fun p => (π.ext p).map Opening.sym)
      (Tr.app (s := (chainsOf C (WholeD.of a W) tF tJ t3).c₁) (t := (chainsOf C (WholeD.of a W) tF
        tJ t3).c₂ ++ (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
        (TypedOracleCompiler.Joined.tr₁ (wholeDesc C (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block))
          (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block)) π A)
        (Tr.app (s := (chainsOf C (WholeD.of a W) tF tJ t3).c₂) (t := (chainsOf C (WholeD.of a W) tF
          tJ t3).c₃)
          (TypedOracleCompiler.Joined.tr₂ (wholeDesc C (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block))
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block)) π B)
          (TypedOracleCompiler.Joined.tr₃ (wholeDesc C (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block))
            (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent (proofRun W ok key c block)) π E))) =
              true := by
  subst hW
  exact accept_threeA C K chal a _ tF tJ t3 silent _ sb cfg pF pJ p3 salt path r π ht A B E hF hK
    hρ G.fits x hsil
    (proofRun_yesA _ ok key c block table r x hok hkey G.roots G.sealed G.okWords hb hyes)

end

/-! ## The reductions as OnBytes/Maker/Files.lean lays them -/

section Large
open _root_.Iop _root_.Compile

/-- **What is asked of tables and transcript**, the draws but for the digests. -/
structure TrHeldA (C : CK) (a : ℕ) (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead)
    (tabs : List (ℕ × List (ℕ × Row3))) (etab : List (ℕ × Row3))
    (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str) (τ₁ : Iop.Tr (uLT C (WholeD.of a W).ds₁))
    (τ₂ : Iop.Tr (uLT C (WholeD.of a W).ds₂)) (τ₃ : Iop.Tr (uLT C (WholeD.of a W).ds₃)) :
    Prop where
  tb : TabsHold W sb r tabs
  ex : ExtHolds a W r etab
  h₁ : HoldsA C (WholeD.of a W).ds₁ 0 tabs r.first.out.rounds.toList.dropLast τ₁
  h₂ : HoldsA C (WholeD.of a W).ds₂ (WholeD.of a W).t₁ tabs r.shared.out.rounds.toList τ₂
  h₃ : HoldsA C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂) tabs
    r.second.out.rounds.toList τ₃
  hy : ∀ (x : ℕ) (hx : x < 2 ^ a) c s pt, etab.lookup x = some (c, s, pt) → y ⟨x, hx⟩ = (x, c)
  work₁ : passT C (WholeD.of a W).ds₁ (rhoT C (WholeD.of a W).ds₁ τ₁) = true
  work₂ : passT C (WholeD.of a W).ds₂ (rhoT C (WholeD.of a W).ds₂ τ₂) = true
  work₃ : passT C (WholeD.of a W).ds₃ (rhoT C (WholeD.of a W).ds₃ τ₃) = true

/-- The two records together. -/
theorem fileHeldA_of {C : CK} {a : ℕ} {W : Three.Whole} {sb : ℕ} {r : Proof.TailRead}
    {tabs : List (ℕ × List (ℕ × Row3))} {etab : List (ℕ × Row3)} {S₁ S₂ S₃ : Fmt.SpecX}
    {y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str} {τ₁ : Iop.Tr (uLT C (WholeD.of a W).ds₁)}
    {τ₂ : Iop.Tr (uLT C (WholeD.of a W).ds₂)} {τ₃ : Iop.Tr (uLT C (WholeD.of a W).ds₃)}
    (F : ReadFits a W r S₁ S₂ S₃) (T : TrHeldA C a W sb r tabs etab y τ₁ τ₂ τ₃) :
    FileHeldA C a W sb r tabs etab S₁ S₂ S₃ y τ₁ τ₂ τ₃ :=
  ⟨T.tb, T.ex, F.shape, F.bare, F.st₁, F.st₂, F.st₃, F.ft₁, F.ft₂, F.ft₃, F.ls₁, F.ls₂, F.ls₃, T.h₁,
    T.h₂, T.h₃, T.hy, F.v₁, F.v₂, F.v₃, F.pw₁, F.pw₂, F.pw₃, T.work₁, T.work₂, T.work₃⟩

section
variable (C : CK) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  {sb : ℕ} {r : Proof.TailRead} {tabs : List (ℕ × List (ℕ × Row3))} {etab : List (ℕ × Row3)}
  {S₁ S₂ S₃ : Fmt.SpecX} {Rs : Rounds × Rounds × Rounds}

/-- A key file, at any data W that are those of the rounds Rs. -/
theorem keyIORAt_of_givesA {R : Type} (W : Three.Whole)
    (hW : W = Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) (G : PortGives a Rs r S₁ S₂ S₃) (ok : Bool)
    (hok : ok = true) (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (table : Params.TableName) (hyes : Key.keyRefusal k table r = none)
    (x : R) (hkey : key x = r.key) (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str)
    (τ : Tr (chainsOf C (WholeD.of a W) tF tJ t3).sh)
    (T : TrHeldA C a W sb r tabs etab y ((chainsOf C (WholeD.of a W) tF tJ t3).tr₁ τ)
      ((chainsOf C (WholeD.of a W) tF tJ t3).tr₂ τ) ((chainsOf C (WholeD.of a W) tF tJ t3).tr₃ τ))
    (hsil : silent x ((chainsOf C (WholeD.of a W) tF tJ t3).msgF τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msgJ τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msg3 τ).2 = true) :
    (keyIORAt C a tF tJ t3 W ok silent key k).out x y τ = some () := by
  subst hW
  exact keyIORAt_yesA C a tF tJ t3 _ ok silent key k table x y τ (fileHeldA_of G.fits T) hsil hok
    hkey G.roots G.sealed G.okWords hyes

/-- A proof file, at any data W that are those of the rounds Rs. -/
theorem proofIORAt_of_givesA {X R : Type} (W : Three.Whole)
    (hW : W = Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) (G : PortGives a Rs r S₁ S₂ S₃) (ok : Bool)
    (hok : ok = true) (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (table : Params.TableName)
    (x : X × R) (hyes : Proof.proofRefusal c table (block x.1) r = none)
    (hb : TwoLaws.Carries (TwoLaws.Alike TwoLaws.AnyGiven false)
      (TwoLaws.FirstEndAlike TwoLaws.AnyGiven) (block x.1) (block x.1))
    (hkey : key x.2 = r.key) (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str)
    (τ : Tr (chainsOf C (WholeD.of a W) tF tJ t3).sh)
    (T : TrHeldA C a W sb r tabs etab y ((chainsOf C (WholeD.of a W) tF tJ t3).tr₁ τ)
      ((chainsOf C (WholeD.of a W) tF tJ t3).tr₂ τ) ((chainsOf C (WholeD.of a W) tF tJ t3).tr₃ τ))
    (hsil : silent x ((chainsOf C (WholeD.of a W) tF tJ t3).msgF τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msgJ τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msg3 τ).2 = true) :
    (proofIORAt C a tF tJ t3 W ok silent key c block).out x y τ = some () := by
  subst hW
  exact proofIORAt_yesA C a tF tJ t3 _ ok silent key c block table x y τ (fileHeldA_of G.fits T)
    hsil
    hok hkey G.roots G.sealed G.okWords hb hyes

end

section
variable (C : CK) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **A key file: the program has read r and its decision on r says yes, so the reduction says yes
at every transcript of which `TrHeldA` holds and at which the silent rounds' test says yes, if the
tests on the rounds pass and the fixed record's dry runs state the same rounds.** r is the caller's
letter. Rs is fixed by the equation on
`dryKey`. -/
theorem keyIOR_of_readA {R : Type} (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray) (j : ℕ)
    (r : Proof.TailRead) (hr : (Key.readKey k table file j).fromStart = .ok r)
    (hno : Key.keyRefusal k table r = none) :
    ∃ Rs : Rounds × Rounds × Rounds, dryKey k r.key = some Rs ∧
      ∀ rec₀ : R, dryKey k (key rec₀) = some Rs → okAt a (some Rs) = true →
        shapesFit a (Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) = true →
        sealBare (Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) = true →
        ∀ (x : R), key x = r.key → ∀ (sb : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
          (etab : List (ℕ × Row3)) (y : (oneExternalString (2 ^ (WholeD.of a (dataAt a (dryKey k (key rec₀)))).a)
            SgX).Str)
          (τ : Tr (chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).sh),
          TrHeldA C a (dataAt a (dryKey k (key rec₀))) sb r tabs etab y
            ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).tr₁ τ)
            ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).tr₂ τ)
            ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).tr₃ τ) →
          silent x ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).msgF τ).2
            ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).msgJ τ).2
            ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).msg3 τ).2 = true →
          (keyIOR C a tF tJ t3 silent key k rec₀).out x y τ = some () := by
  obtain ⟨-, Rs, hd, G⟩ := key_read_gives a k table file j r hr hno
  refine ⟨Rs, hd, fun rec₀ h0 hok hsh hb x hkey sb tabs etab y τ T hsil => ?_⟩
  obtain ⟨S₁, S₂, S₃, G'⟩ := G hok hsh hb
  exact keyIORAt_of_givesA C a tF tJ t3 (dataAt a (dryKey k (key rec₀)))
    (by rw [h0]; exact dataAt_of_ok hok) G' _ (by rw [h0]; exact hok) silent key k
    table hno x hkey y τ T hsil

/-- **A proof file: the same**, if also the instance's block is b and has the law's relation. b: the
first chain's block under which the file was read. -/
theorem proofIOR_of_readA {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (table : Params.TableName)
    (copy : ℕ) (request words : ByteArray) (b : Blk Proof.FirstEnd) (file : ByteArray)
    (r : Proof.TailRead) (hr : (Proof.readProof c table copy request words b file).fromStart = .ok
        r)
    (hno : Proof.proofRefusal c table b r = none) :
    ∃ Rs : Rounds × Rounds × Rounds, dryProof c r.key b = some Rs ∧
      ∀ z₀ : X × R, dryProof c (key z₀.2) (block z₀.1) = some Rs → okAt a (some Rs) = true →
        shapesFit a (Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) = true →
        sealBare (Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) = true →
        ∀ (x : X × R), block x.1 = b →
          TwoLaws.Carries (TwoLaws.Alike TwoLaws.AnyGiven false)
            (TwoLaws.FirstEndAlike TwoLaws.AnyGiven) (block x.1) (block x.1) →
          key x.2 = r.key → ∀ (sb : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
          (etab : List (ℕ × Row3)) (y : (oneExternalString (2 ^ (WholeD.of a (dataAt a (dryProof c (key z₀.2)
                         (block z₀.1)))).a) SgX).Str)
          (τ : Tr (chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
            t3).sh),
          TrHeldA C a (dataAt a (dryProof c (key z₀.2) (block z₀.1))) sb r tabs etab y
            ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ t3).tr₁
              τ)
            ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ t3).tr₂
              τ)
            ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ t3).tr₃
              τ) →
          silent x ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
            t3).msgF τ).2
            ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
              t3).msgJ τ).2
            ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
              t3).msg3 τ).2 = true →
          (proofIOR C a tF tJ t3 silent key c block z₀).out x y τ = some () := by
  obtain ⟨-, Rs, hd, G⟩ := proof_read_gives a c table copy request words b file r hr hno
  refine ⟨Rs, hd, fun z₀ h0 hok hsh hb x hbl hc hkey sb tabs etab y τ T hsil => ?_⟩
  obtain ⟨S₁, S₂, S₃, G'⟩ := G hok hsh hb
  exact proofIORAt_of_givesA C a tF tJ t3 (dataAt a (dryProof c (key z₀.2) (block z₀.1)))
    (by rw [h0]; exact dataAt_of_ok hok) G' _ (by rw [h0]; exact hok) silent key c
    block table x (by rw [hbl]; exact hno) hc hkey y τ T hsil

/-- **A key file, from the check's yes**, under the conditions of `keyIOR_of_readA`. j and r are
fixed by the two equations: r is the reading that the check itself has made. -/
theorem keyIOR_of_checkA {R : Type} (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (file : ByteArray) (table : Params.TableName)
    (h : Key.check k file = .ok table) :
    ∃ j r, Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file = .ok (table, j) ∧
      (Key.readKey k table file j).fromStart = .ok r ∧
      ∃ Rs : Rounds × Rounds × Rounds, dryKey k r.key = some Rs ∧
        ∀ rec₀ : R, dryKey k (key rec₀) = some Rs → okAt a (some Rs) = true →
          shapesFit a (Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) = true →
          sealBare (Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) = true →
          ∀ (x : R), key x = r.key → ∀ (sb : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
            (etab : List (ℕ × Row3)) (y : (oneExternalString (2 ^ (WholeD.of a (dataAt a (dryKey k (key
                           rec₀)))).a) SgX).Str)
            (τ : Tr (chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).sh),
            TrHeldA C a (dataAt a (dryKey k (key rec₀))) sb r tabs etab y
              ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).tr₁ τ)
              ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).tr₂ τ)
              ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).tr₃ τ) →
            silent x ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).msgF τ).2
              ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).msgJ τ).2
              ((chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).msg3 τ).2 = true
                →
            (keyIOR C a tF tJ t3 silent key k rec₀).out x y τ = some () := by
  obtain ⟨j, r, ht, hr, hno⟩ := key_check_reads k file table h
  exact ⟨j, r, ht, hr, keyIOR_of_readA C a tF tJ t3 silent key k table file j r hr hno⟩

/-- **A proof file, from the check's yes**, under the conditions of `proofIOR_of_readA`. r is fixed
by the equation. -/
theorem proofIOR_of_checkA {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (table : Params.TableName)
    (copy : ℕ) (request words : ByteArray) (reply : E) (links : Blk Proof.LinksResult)
    (file : ByteArray) (h : Proof.check c table copy request words reply links file = .accepted) :
    ∃ r, (Proof.readProof c table copy request words (Proof.firstBlock c.first links reply)
        file).fromStart = .ok r ∧
      ∃ Rs : Rounds × Rounds × Rounds, dryProof c r.key (Proof.firstBlock c.first links reply) =
        some Rs ∧
        ∀ z₀ : X × R, dryProof c (key z₀.2) (block z₀.1) = some Rs → okAt a (some Rs) = true →
          shapesFit a (Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) = true →
          sealBare (Three.Whole.of Rs.1 Rs.2.1 Rs.2.2) = true →
          ∀ (x : X × R), block x.1 = Proof.firstBlock c.first links reply →
            TwoLaws.Carries (TwoLaws.Alike TwoLaws.AnyGiven false)
              (TwoLaws.FirstEndAlike TwoLaws.AnyGiven) (block x.1) (block x.1) →
            key x.2 = r.key → ∀ (sb : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
            (etab : List (ℕ × Row3)) (y : (oneExternalString (2 ^ (WholeD.of a (dataAt a (dryProof c (key z₀.2)
                           (block z₀.1)))).a) SgX).Str)
            (τ : Tr (chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
              t3).sh),
            TrHeldA C a (dataAt a (dryProof c (key z₀.2) (block z₀.1))) sb r tabs etab y
              ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
                t3).tr₁ τ)
              ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
                t3).tr₂ τ)
              ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
                t3).tr₃ τ) →
            silent x ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF
              tJ t3).msgF τ).2
              ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
                t3).msgJ τ).2
              ((chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ
                t3).msg3 τ).2 = true →
            (proofIOR C a tF tJ t3 silent key c block z₀).out x y τ = some () := by
  obtain ⟨r, hr, hno⟩ := proof_check_reads c table copy request words reply links file h
  exact ⟨r, hr, proofIOR_of_readA C a tF tJ t3 silent key c block table copy request words _ file r
      hr
    hno⟩

end

end Large

end OnBytes.Maker
