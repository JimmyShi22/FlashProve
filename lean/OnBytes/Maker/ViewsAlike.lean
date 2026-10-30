-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ViewsAlike.lean: the three views that the reduction of a whole file forms of a typed
transcript are the strict reader's views of the file's three chains, the first without its last
round, but for the digests drawn; and where the verifier program's decision says yes, that reduction
says yes at every transcript that holds what was read, if also the silent rounds' test says yes at
the transcript's three messages, the tests' verdict is yes, the instance's record is written as the
key read, the data count the first chain's roots as read, the first view ends in a sealing round,
the key and the three views as read pass the tests on the words (`okRead`,
OnBytes/Maker/Decide3Laws.lean), and, for a proof file, the first chain's block carries the law's
relation.

A round of the kind "sealed" draws a digest. In the joined protocol of a file the typed verifier's
message of such a round need not hold the digest that the strict reader has drawn. No block's run
reads that digest: that is the law "blind" on the blocks as programs (OnBytes/TypedOracleCompiler/Laws/); of a proof
file's first block it is asked (`hb`). It is what
`decideKey_iff` and `decideProof_iff` (OnBytes/Maker/Decide3Laws.lean) call. So here a transcript is
asked to give the draws read "but for the digests" (`DrawnAlike`, OnBytes/TypedOracleCompiler/Laws/LawAlike.lean),
round by round. The three views are then the strict reader's but for the digests drawn (`ViewAlike`,
OnBytes/TypedOracleCompiler/Laws/LawRun.lean), and that is what the laws on the program's decision take
(OnBytes/Maker/Decide3Laws.lean).

Main definitions.
  `HoldsA`: a stretch of a transcript holds what was read: its plain parts are those typed from the
    rounds read; its verifier's messages give the draws read, but for the digests; at a position
    where `opensT` has an opening it holds that opening's symbol.
  `FileHeldA`: a transcript and a stored table's string hold a file as read: all hypotheses on
    tables, data, reading and transcript in one record, two tests on the data and the three proofs
    of work at the transcript's own messages among them.
Main theorems.
  `wantsOf_poss`, `fullOf_poss`: what the drawn positions ask for, and the test on the parts, read
    the positions alone.
  `rvT_alike`: the rounds of a view, but for the digests.
  `view_alike`: one chain's view. `views_alike`: the three.
  `viewAlike_trans`, `withSeal_alike`: two laws on `ViewAlike`.
  `whole_yesA`: the verifier's yes, if the run says yes at all views that are the file's but for
    digests, the first without its last round.
  `keyRun_yesA`, `proofRun_yesA`: that premise, from the program's yes.
  `keyIORAt_yesA`, `proofIORAt_yesA`: the two files.

What is not claimed. None of the hypotheses. Nothing on soundness.


-/
import OnBytes.Maker.AcceptOfYes

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Compile _root_.Run _root_.Run.PQ OnBytes.TwoLaws

/-! ## What reads the positions alone -/

/-- What the drawn positions ask for does not read the digests. -/
theorem wantsOf_poss (a : ℕ) (dep : ℕ → Option ℕ) : ∀ (ds : List RDT) {Rs Rs' : List Fmt.Drawn},
    LAlike DrawnAlike Rs Rs' → wantsOf a dep ds Rs = wantsOf a dep ds Rs'
  | [], _, _, _ => rfl
  | _ :: _, _, _, .nil => rfl
  | d :: ds, _, _, .cons h t => by
    rw [wantsOf_cons, wantsOf_cons, h.poss, wantsOf_poss a dep ds t]

/-- Nor does the test on the parts. -/
theorem fullOf_poss : ∀ (ds : List RDT) {Rs Rs' : List Fmt.Drawn},
    LAlike DrawnAlike Rs Rs' → fullOf ds Rs = fullOf ds Rs'
  | [], _, _, _ => rfl
  | _ :: _, _, _, .nil => rfl
  | d :: ds, R :: Rs, R' :: Rs', .cons h t => by
    show ((d.stored.all fun s => (Fmt.partOf s R.poss).length == s.count) && fullOf ds Rs) =
      ((d.stored.all fun s => (Fmt.partOf s R'.poss).length == s.count) && fullOf ds Rs')
    rw [h.poss, fullOf_poss ds t]

/-! ## The transcript -/

/-- A stretch's part of a transcript holds what was read, the draws but for the digests. -/
structure HoldsA (C : CK) (ds : List RDT) (base : ℕ) (tabs : List (ℕ × List (ℕ × Row3)))
    (ros : List Fmt.RoundOut) (τ : Iop.Tr (uLT C ds)) : Prop where
  plains : plainsT C ds ros = some τ.plains
  drawn : LAlike DrawnAlike (ros.map (·.drawn)) (drawnT C ds τ.rho)
  read : ∀ p op, opensT C ds base tabs p = some op → τ.read p = op.sym

/-- **The rounds of the view, but for the digests.** -/
theorem rvT_alike (C : CK) :
    ∀ (ds : List RDT) (ros : List Fmt.RoundOut) (τ : Iop.Tr (uLT C ds)),
      plainsT C ds ros = some τ.plains →
      LAlike DrawnAlike (ros.map (·.drawn)) (drawnT C ds τ.rho) →
      LAlike RVAlike (ros.map fun r => (⟨Fmt.noRoots r.vals, r.drawn⟩ : RV)) (rvT C ds τ)
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, h, _ => by simp [plainsT] at h
  | _ :: _, [], _, h, _ => by simp [plainsT] at h
  | d :: ds, ro :: ros, (m, c, τ), h, hd => by
      rcases h1 : PlainOf.ofGots d.items ro.vals with _ | p0
      · simp [plainsT, h1] at h
      rcases h2 : plainsT C ds ros with _ | pl0
      · simp [plainsT, h1, h2] at h
      simp only [plainsT, h1, h2, Option.some.injEq] at h
      have e1 : GPlain.mk d.entry.work p0 ro.nonce = m.2 := congrArg Prod.fst h
      have e2 : pl0 = τ.plains := congrArg Prod.snd h
      cases hd with
      | cons hd1 hd2 =>
        show LAlike RVAlike ((⟨Fmt.noRoots ro.vals, ro.drawn⟩ : RV) :: _)
          ((⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ : RV) :: rvT C ds τ)
        rw [← e1, pv_old_mk, gots_ofGots _ _ _ h1]
        exact .cons ⟨rfl, hd1⟩ (rvT_alike C ds ros τ (e2 ▸ h2) hd2)

section
variable (C : CK) (D : WholeD) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Iop.Tr (uLT C D.ds₁))
  (τ₂ : Iop.Tr (uLT C D.ds₂)) (τ₃ : Iop.Tr (uLT C D.ds₃))

/-- **One chain's view is the strict reader's list of rounds and of opened columns, but for the
digests drawn.** -/
theorem view_alike (key : ℕ → ℕ) (first : ℕ) {ds : List RDT} {ros : List Fmt.RoundOut}
    (τ : Iop.Tr (uLT C ds)) (hpl : plainsT C ds ros = some τ.plains)
    (hd : LAlike DrawnAlike (ros.map (·.drawn)) (drawnT C ds τ.rho))
    (h : List.Forall₂ (RoundFits D.a D.depth key first (colOf C D y τ₁ τ₂ τ₃)) ds ros) :
    ViewAlike
      ⟨ros.map fun r => ⟨Fmt.noRoots r.vals, r.drawn⟩,
        ((ds.map (·.stored)).zip ros).flatMap fun u => Fmt.openedX first u.1 u.2⟩
      (viewOf C D y τ₁ τ₂ τ₃ (rvT C ds τ) key
        (wantsOf D.a D.depth ds (drawnT C ds (rhoT C ds τ)))) := by
  refine ⟨rvT_alike C ds ros τ hpl hd, ?_⟩
  rw [rhoT_eq, ← wantsOf_poss D.a D.depth ds hd]
  exact (viewOf_opened C D y τ₁ τ₂ τ₃ (rvT C ds τ) key first h).symm

end

/-! ## Two laws on views that are alike -/

theorem drawnAlike_trans {a b c : Fmt.Drawn} (h : DrawnAlike a b) (k : DrawnAlike b c) :
    DrawnAlike a c :=
  ⟨h.elems.trans k.elems, h.poss.trans k.poss, h.trits.trans k.trits⟩

theorem lAlike_trans {α : Type} {P : α → α → Prop} (hP : ∀ a b c, P a b → P b c → P a c) :
    ∀ {l m n : List α}, LAlike P l m → LAlike P m n → LAlike P l n
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons (hP _ _ _ h h') (lAlike_trans hP t t')

/-- Alike to a view that is alike to a third. -/
theorem viewAlike_trans {u v w : Fmt.View} (h : ViewAlike u v) (k : ViewAlike v w) :
    ViewAlike u w :=
  ⟨lAlike_trans (fun _ _ _ p q => ⟨p.vals.trans q.vals, drawnAlike_trans p.drawn q.drawn⟩) h.rounds
    k.rounds, h.opened.trans k.opened⟩

/-- The sealing round put back behind two views that are alike. -/
theorem withSeal_alike {u v : Fmt.View} (h : ViewAlike u v) :
    ViewAlike (withSeal u) (withSeal v) :=
  ⟨h.rounds.append (.cons ⟨rfl, DrawnAlike.refl _⟩ .nil), h.opened⟩

/-! ## The whole file -/

/-- **A transcript and a stored table's string hold a file as read, the draws but for the digests.**
-/
structure FileHeldA (C : CK) (a : ℕ) (W : Three.Whole) (sb : ℕ) (r : Proof.TailRead)
    (tabs : List (ℕ × List (ℕ × Row3))) (etab : List (ℕ × Row3)) (S₁ S₂ S₃ : Fmt.SpecX)
    (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str) (τ₁ : Iop.Tr (uLT C (WholeD.of a W).ds₁))
    (τ₂ : Iop.Tr (uLT C (WholeD.of a W).ds₂)) (τ₃ : Iop.Tr (uLT C (WholeD.of a W).ds₃)) :
    Prop where
  tb : TabsHold W sb r tabs
  ex : ExtHolds a W r etab
  shape : shapesFit a W = true
  bare : sealBare W = true
  st₁ : S₁.stored = W.ds₁.map (·.stored)
  st₂ : S₂.stored = W.ds₂.map (·.stored)
  st₃ : S₃.stored = W.ds₃.map (·.stored)
  ft₁ : S₁.base.firstTree = 0
  ft₂ : S₂.base.firstTree = 0
  ft₃ : S₃.base.firstTree = Three.first₃ W.t₁
  ls₁ : ListedAsDrawn a W.ds₁ r.first.out.rounds.toList
  ls₂ : ListedAsDrawn a W.ds₂ r.shared.out.rounds.toList
  ls₃ : ListedAsDrawn a W.ds₃ r.second.out.rounds.toList
  h₁ : HoldsA C (WholeD.of a W).ds₁ 0 tabs r.first.out.rounds.toList.dropLast τ₁
  h₂ : HoldsA C (WholeD.of a W).ds₂ (WholeD.of a W).t₁ tabs r.shared.out.rounds.toList τ₂
  h₃ : HoldsA C (WholeD.of a W).ds₃ ((WholeD.of a W).t₁ + (WholeD.of a W).t₂) tabs
    r.second.out.rounds.toList τ₃
  hy : ∀ (x : ℕ) (hx : x < 2 ^ a) c s pt, etab.lookup x = some (c, s, pt) → y ⟨x, hx⟩ = (x, c)
  v₁ : r.first.view = Fmt.viewX S₁ r.first.out
  v₂ : r.shared.view = Fmt.viewX S₂ r.shared.out
  v₃ : r.second.view = Fmt.viewX S₃ r.second.out
  pw₁ : PartsWithin W.ds₁ r.first.out.rounds.toList
  pw₂ : PartsWithin W.ds₂ r.shared.out.rounds.toList
  pw₃ : PartsWithin W.ds₃ r.second.out.rounds.toList
  work₁ : passT C (WholeD.of a W).ds₁ (rhoT C (WholeD.of a W).ds₁ τ₁) = true
  work₂ : passT C (WholeD.of a W).ds₂ (rhoT C (WholeD.of a W).ds₂ τ₂) = true
  work₃ : passT C (WholeD.of a W).ds₃ (rhoT C (WholeD.of a W).ds₃ τ₃) = true

section
variable (C : CK) (a : ℕ) (W : Three.Whole) {sb : ℕ} {r : Proof.TailRead}
  {tabs : List (ℕ × List (ℕ × Row3))} {etab : List (ℕ × Row3)} {S₁ S₂ S₃ : Fmt.SpecX}
  (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str) (τ₁ : Iop.Tr (uLT C (WholeD.of a W).ds₁))
  (τ₂ : Iop.Tr (uLT C (WholeD.of a W).ds₂)) (τ₃ : Iop.Tr (uLT C (WholeD.of a W).ds₃))

/-- **The file's three views as read, the first without its last round, are alike to the three views
of the reduction of a whole file.** The right sides are the three views in the text of `reductionOfWholeFile`
(OnBytes/Maker/Whole.lean). -/
theorem views_alike (H : FileHeldA C a W sb r tabs etab S₁ S₂ S₃ y τ₁ τ₂ τ₃) :
    ViewAlike (dropSeal r.first.view)
      (viewOf C (WholeD.of a W) y τ₁ τ₂ τ₃ (rvT C (WholeD.of a W).ds₁ τ₁) (WholeD.of a W).key₁
        (wantsOf (WholeD.of a W).a (WholeD.of a W).depth (WholeD.of a W).ds₁
          (drawnT C (WholeD.of a W).ds₁ (rhoT C (WholeD.of a W).ds₁ τ₁)))) ∧
    ViewAlike r.shared.view
      (viewOf C (WholeD.of a W) y τ₁ τ₂ τ₃ (rvT C (WholeD.of a W).ds₂ τ₂) (WholeD.of a W).key₂
        (wantsOf (WholeD.of a W).a (WholeD.of a W).depth (WholeD.of a W).ds₂
          (drawnT C (WholeD.of a W).ds₂ (rhoT C (WholeD.of a W).ds₂ τ₂)))) ∧
    ViewAlike r.second.view
      (viewOf C (WholeD.of a W) y τ₁ τ₂ τ₃ (rvT C (WholeD.of a W).ds₃ τ₃) (WholeD.of a W).key₃
        (wantsOf (WholeD.of a W).a (WholeD.of a W).depth (WholeD.of a W).ds₃
          (drawnT C (WholeD.of a W).ds₃ (rhoT C (WholeD.of a W).ds₃ τ₃)))) := by
  have hfit := H.tb.fits
  unfold fitsW at hfit
  simp only [Bool.and_eq_true] at hfit
  obtain ⟨n₁, o₁⟩ := roundsFit_spec hfit.1.1
  obtain ⟨n₂, o₂⟩ := roundsFit_spec hfit.1.2
  obtain ⟨n₃, o₃⟩ := roundsFit_spec hfit.2
  have fits := chain_fits C a W sb r tabs etab y τ₁ τ₂ τ₃ H.tb H.ex H.shape H.h₁.read H.h₂.read
    H.h₃.read H.hy
  have smap : ∀ l : List Three.RDL, (l.map rdtOf).map (·.stored) = l.map (·.stored) := fun l => by
    rw [List.map_map]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have hseal := H.bare
    unfold sealBare at hseal
    cases hg : W.ds₁.getLast? with
    | none => rw [hg] at hseal; cases hseal
    | some dl =>
      rw [hg] at hseal
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hseal
      obtain ⟨b, e1, e2, hb⟩ := split_last W.ds₁ r.first.out.rounds.toList n₁ dl hg
      have hob : b.opens = [] := by
        have := o₁ (dl, b) hb
        rw [hseal.1, hseal.2] at this
        exact List.eq_nil_of_length_eq_zero this
      have nd : W.ds₁.dropLast.length = r.first.out.rounds.toList.dropLast.length := by
        rw [List.length_dropLast, List.length_dropLast, n₁]
      have sub := mem_zip_dropLast W.ds₁ r.first.out.rounds.toList n₁
      have F := fits 0 W.ds₁.dropLast r.first.out.rounds.toList.dropLast nd
        (fun p hp => o₁ p (sub p hp))
        (fun p hp q hq => List.mem_append_left _ (List.mem_flatMap.2 ⟨p, sub p hp, hq⟩))
        (fun p hp q hq => List.mem_append_left _ (List.mem_flatMap.2 ⟨p, sub p hp, hq⟩))
        (fun p hp => H.ls₁ p (sub p hp))
      have e := view_alike C (WholeD.of a W) y τ₁ τ₂ τ₃ (W.key 0) 0
        (ds := (WholeD.of a W).ds₁) τ₁ H.h₁.plains H.h₁.drawn F
      have e4 : dropSeal r.first.view = lessLast (Fmt.viewX S₁ r.first.out) := by
        rw [H.v₁]
        rfl
      rw [e4, viewX_less S₁ r.first.out _ b (W.ds₁.dropLast.map (·.stored)) dl.stored e2
        (by
          have e3 := congrArg (List.map fun x : Three.RDL => x.stored) e1
          rw [List.map_append] at e3
          rw [H.st₁]
          exact e3)
        (by rw [List.length_map]; exact nd) hob, H.ft₁, ← smap W.ds₁.dropLast]
      exact e
  · have F := fits 1 W.ds₂ r.shared.out.rounds.toList n₂ o₂
      (fun p hp q hq => List.mem_append_right _
        (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hp, hq⟩)))
      (fun p hp q hq => List.mem_append_right _
        (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hp, hq⟩))) H.ls₂
    have e := view_alike C (WholeD.of a W) y τ₁ τ₂ τ₃ (W.key 1) 0
      (ds := (WholeD.of a W).ds₂) τ₂ H.h₂.plains H.h₂.drawn F
    rw [H.v₂]
    show ViewAlike ⟨_, (S₂.stored.zip _).flatMap fun u => Fmt.openedX S₂.base.firstTree u.1 u.2⟩ _
    rw [H.st₂, H.ft₂, ← smap W.ds₂]
    exact e
  · have F := fits 2 W.ds₃ r.second.out.rounds.toList n₃ o₃
      (fun p hp q hq => List.mem_append_right _
        (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, hq⟩)))
      (fun p hp q hq => List.mem_append_right _
        (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, hq⟩))) H.ls₃
    have e := view_alike C (WholeD.of a W) y τ₁ τ₂ τ₃ (W.key 2) (Three.first₃ W.t₁)
      (ds := (WholeD.of a W).ds₃) τ₃ H.h₃.plains H.h₃.drawn F
    rw [H.v₃]
    show ViewAlike ⟨_, (S₃.stored.zip _).flatMap fun u => Fmt.openedX S₃.base.firstTree u.1 u.2⟩ _
    rw [H.st₃, H.ft₃, ← smap W.ds₃]
    exact e

end

section
variable (C : CK) (a : ℕ) (W : Three.Whole) {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  {sb : ℕ} {r : Proof.TailRead} {tabs : List (ℕ × List (ℕ × Row3))} {etab : List (ℕ × Row3)}
  {S₁ S₂ S₃ : Fmt.SpecX}

/-- **The verifier of the reduction of a whole file says yes**, if the run says yes at all views
that are the file's own but for the digests drawn, the first without its last round. -/
theorem whole_yesA (x : Xi) (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str)
    (τ : Tr (chainsOf C (WholeD.of a W) tF tJ t3).sh)
    (H : FileHeldA C a W sb r tabs etab S₁ S₂ S₃ y
      ((chainsOf C (WholeD.of a W) tF tJ t3).tr₁ τ) ((chainsOf C (WholeD.of a W) tF tJ t3).tr₂ τ)
      ((chainsOf C (WholeD.of a W) tF tJ t3).tr₃ τ))
    (hsil : silent x ((chainsOf C (WholeD.of a W) tF tJ t3).msgF τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msgJ τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msg3 τ).2 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal r.first.view) v₁ → ViewAlike r.shared.view v₂ →
      ViewAlike r.second.view v₃ → run x v₁ v₂ v₃ = true) :
    (reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent run).out x y τ = some () := by
  obtain ⟨e1, e2, e3⟩ := views_alike C a W y _ _ _ H
  have hfit := H.tb.fits
  unfold fitsW at hfit
  simp only [Bool.and_eq_true] at hfit
  obtain ⟨n₁, o₁⟩ := roundsFit_spec hfit.1.1
  obtain ⟨-, o₂⟩ := roundsFit_spec hfit.1.2
  obtain ⟨-, o₃⟩ := roundsFit_spec hfit.2
  have sub := mem_zip_dropLast W.ds₁ r.first.out.rounds.toList n₁
  have d1 := H.h₁.drawn
  have d2 := H.h₂.drawn
  have d3 := H.h₃.drawn
  rw [← rhoT_eq] at d1 d2 d3
  have f1 := fullOf_of_within W.ds₁.dropLast r.first.out.rounds.toList.dropLast
    fun p hp => H.pw₁ p (sub p hp)
  have f2 := fullOf_of_within W.ds₂ _ H.pw₂
  have f3 := fullOf_of_within W.ds₃ _ H.pw₃
  have c1 := carries_chain a W r etab y H.ex H.hy W.ds₁.dropLast
    r.first.out.rounds.toList.dropLast (fun p hp => o₁ p (sub p hp))
    (fun p hp q hq => List.mem_append_left _ (List.mem_flatMap.2 ⟨p, sub p hp, hq⟩))
    (fun p hp => H.ls₁ p (sub p hp))
  have c2 := carries_chain a W r etab y H.ex H.hy W.ds₂ _ o₂
    (fun p hp q hq => List.mem_append_right _
      (List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hp, hq⟩))) H.ls₂
  have c3 := carries_chain a W r etab y H.ex H.hy W.ds₃ _ o₃
    (fun p hp q hq => List.mem_append_right _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, hq⟩))) H.ls₃
  rw [fullOf_poss _ d1] at f1
  rw [fullOf_poss _ d2] at f2
  rw [fullOf_poss _ d3] at f3
  rw [wantsOf_poss _ _ _ d1] at c1
  rw [wantsOf_poss _ _ _ d2] at c2
  rw [wantsOf_poss _ _ _ d3] at c3
  refine if_pos ?_
  rw [carriesOf_append, carriesOf_append]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨H.work₁, H.work₂⟩, H.work₃⟩, f1⟩, f2⟩, f3⟩, c1, c2, c3⟩, hsil⟩, hrun _ _ _ e1 e2 e3⟩

end

/-! ## The run's yes from the program's yes -/

/-- The run of a key file's reduction says yes at all views that are the file's own but for the
digests drawn, where the program's decision on the file says yes. -/
theorem keyRun_yesA {R : Type} (W : Three.Whole) (ok : Bool) (key : R → TableKey)
    (k : Params.KeyChains) (table : Params.TableName) (r : Proof.TailRead) (x : R)
    (hok : ok = true) (hkey : key x = r.key) (hroots : W.t₁ = r.first.roots.length)
    (hseal : SealedLast r.first.view) (hw : okRead r = true)
    (hyes : Key.keyRefusal k table r = none)
    (v₁ v₂ v₃ : View) (h1 : ViewAlike (dropSeal r.first.view) v₁) (h2 : ViewAlike r.shared.view v₂)
    (h3 : ViewAlike r.second.view v₃) :
    (ok && decideKey k (key x) W.t₁ W.t₂ v₁ v₂ v₃) = true := by
  rw [hok, hkey, hroots, Bool.true_and, decideKey_iff k table r W.t₂
    (viewAlike_trans (viewAlike_withSeal hseal) (withSeal_alike h1)) h2 h3, hyes, hw]
  rfl

/-- The same for a proof file. -/
theorem proofRun_yesA {X R : Type} (W : Three.Whole) (ok : Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (table : Params.TableName)
    (r : Proof.TailRead) (x : X × R) (hok : ok = true) (hkey : key x.2 = r.key)
    (hroots : W.t₁ = r.first.roots.length) (hseal : SealedLast r.first.view)
    (hw : okRead r = true)
    (hb : Carries (Alike AnyGiven false) (FirstEndAlike AnyGiven) (block x.1) (block x.1))
    (hyes : Proof.proofRefusal c table (block x.1) r = none)
    (v₁ v₂ v₃ : View) (h1 : ViewAlike (dropSeal r.first.view) v₁) (h2 : ViewAlike r.shared.view v₂)
    (h3 : ViewAlike r.second.view v₃) :
    (ok && decideProof c (key x.2) (block x.1) W.t₁ W.t₂ v₁ v₂ v₃) = true := by
  have h : Proof.refusalOn c table (block x.1) r.first.view r = none := by
    rw [Proof.proofRefusal_eq] at hyes
    exact hyes
  rw [hok, hkey, hroots, Bool.true_and, decideProof_iff c table hb r W.t₂
    (viewAlike_trans (viewAlike_withSeal hseal) (withSeal_alike h1)) h2 h3, h]
  show (okRead r && true) = true
  rw [hw]
  rfl

/-! ## The two files -/

section
variable (C : CK) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) (W : Three.Whole)
  {sb : ℕ} {r : Proof.TailRead} {tabs : List (ℕ × List (ℕ × Row3))} {etab : List (ℕ × Row3)}
  {S₁ S₂ S₃ : Fmt.SpecX}

/-- **A key file: the program's yes gives the reduction's yes.** -/
theorem keyIORAt_yesA {R : Type} (ok : Bool) (silent : R → TF → TJ → T3 → Bool)
    (key : R → TableKey) (k : Params.KeyChains) (table : Params.TableName) (x : R)
    (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str) (τ : Tr (chainsOf C (WholeD.of a W) tF tJ t3).sh)
    (H : FileHeldA C a W sb r tabs etab S₁ S₂ S₃ y
      ((chainsOf C (WholeD.of a W) tF tJ t3).tr₁ τ) ((chainsOf C (WholeD.of a W) tF tJ t3).tr₂ τ)
      ((chainsOf C (WholeD.of a W) tF tJ t3).tr₃ τ))
    (hsil : silent x ((chainsOf C (WholeD.of a W) tF tJ t3).msgF τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msgJ τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msg3 τ).2 = true)
    (hok : ok = true) (hkey : key x = r.key) (hroots : W.t₁ = r.first.roots.length)
    (hseal : SealedLast r.first.view) (hw : okRead r = true)
    (hyes : Key.keyRefusal k table r = none) :
    (keyIORAt C a tF tJ t3 W ok silent key k).out x y τ = some () :=
  whole_yesA C a W tF tJ t3 silent
    (fun (rec : R) v₁ v₂ v₃ => ok && decideKey k (key rec) W.t₁ W.t₂ v₁ v₂ v₃) x y τ H hsil
    (keyRun_yesA W ok key k table r x hok hkey hroots hseal hw hyes)

/-- **A proof file: the program's yes gives the reduction's yes.** -/
theorem proofIORAt_yesA {X R : Type} (ok : Bool) (silent : X × R → TF → TJ → T3 → Bool)
    (key : R → TableKey) (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd)
    (table : Params.TableName) (x : X × R) (y : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Str)
    (τ : Tr (chainsOf C (WholeD.of a W) tF tJ t3).sh)
    (H : FileHeldA C a W sb r tabs etab S₁ S₂ S₃ y
      ((chainsOf C (WholeD.of a W) tF tJ t3).tr₁ τ) ((chainsOf C (WholeD.of a W) tF tJ t3).tr₂ τ)
      ((chainsOf C (WholeD.of a W) tF tJ t3).tr₃ τ))
    (hsil : silent x ((chainsOf C (WholeD.of a W) tF tJ t3).msgF τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msgJ τ).2
      ((chainsOf C (WholeD.of a W) tF tJ t3).msg3 τ).2 = true)
    (hok : ok = true) (hkey : key x.2 = r.key) (hroots : W.t₁ = r.first.roots.length)
    (hseal : SealedLast r.first.view) (hw : okRead r = true)
    (hb : Carries (Alike AnyGiven false) (FirstEndAlike AnyGiven) (block x.1) (block x.1))
    (hyes : Proof.proofRefusal c table (block x.1) r = none) :
    (proofIORAt C a tF tJ t3 W ok silent key c block).out x y τ = some () :=
  whole_yesA C a W tF tJ t3 silent
    (fun (z : X × R) v₁ v₂ v₃ => ok && decideProof c (key z.2) (block z.1) W.t₁ W.t₂ v₁ v₂ v₃)
    x y τ H hsil (proofRun_yesA W ok key c block table r x hok hkey hroots hseal hw hb hyes)

end

end OnBytes.Maker
