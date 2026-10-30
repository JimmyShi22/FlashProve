-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/TieK/LinksEnd.lean: the list of links that the program runs on a request ends in the output
head's link.

"The program" is the Lean program verify-on-bytes. Its stage request runs a list of links that it
joins from two lists, member by member (requestRun in OnBytes/Model/VerifyStages.lean): the records
come from the links as built, which have passed the public tests (builtOf), and each link's routine
comes from the links made for the request (linksOf). This file shows that the joined list ends in a
link of kind 2 whose routine is the head's, for the request's covered positions.

How. The function that lists the links (listLinksH in OnBytes/Model/StagesLinks.lean) pushes the
head's link last, with kind 2. The kinds of the links before it depend on the number of groups of
layers, on whether the proof covers attention and on the plans for attention alone, not on the
request: so the two lists have the same kinds, and the same length. The public tests hand the links
on with one field filled (declareLinks): number, order and all other fields stay.

Main definitions: kindsL (the kinds of the links before the head's).
Main theorems: ok_of_bind, ok_of_jp, forIn_keeps, zipIdx_map_fst, zipIdx_at, zipWith_snoc,
snoc_of_map, map_push (tools); listLinksH_kinds; declareLinks_keeps, buildLinksH_keeps; links_end.

What is not claimed. Nothing on the other fields of a link. That the functions return a value is a
hypothesis. It claims nothing on soundness. The program does not import this file.
-/
import OnBytes.Model.VerifyStages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK

open OnBytes.Model.Stages (LinkH SubPlanH FrameLink)

/-! ## Tools -/

/-- If a step and what follows it return a value, the step has returned one, and what follows
returns the value from it. -/
theorem ok_of_bind {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- If "refuse under a condition, then go on" returns a value, the condition is false and what
follows returns the value. -/
theorem ok_of_jp {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- A loop over a list in which every step goes on: what holds of the members taken so far and the
state at the start, and is kept by each step, holds of the whole list and the state at the end. The
step may use where in the list it stands. -/
theorem forIn_keeps {α σ : Type} (f : α → σ → Except String (ForInStep σ)) (l0 : List α)
    (I : List α → σ → Prop)
    (step : ∀ pre a rest, l0 = pre ++ a :: rest → ∀ s s', I pre s → f a s = .ok s' →
      ∃ t, s' = .yield t ∧ I (pre ++ [a]) t) :
    ∀ (l pre : List α) (s r : σ), l0 = pre ++ l → I pre s → forIn l s f = .ok r → I l0 r
  | [], pre, s, r, e, hI, h => by
    rw [List.forIn_nil] at h
    have hr : s = r := Except.ok.inj h
    rw [e, List.append_nil, ← hr]
    exact hI
  | a :: l, pre, s, r, e, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := ok_of_bind h
    obtain ⟨t, rfl, hI'⟩ := step pre a l e s s' hI hs
    exact forIn_keeps f l0 I step l (pre ++ [a]) t r (by rw [e]; simp) hI' h

/-- A function of the members alone, mapped over a list with numbers. -/
theorem zipIdx_map_fst {α β : Type} (f : α → β) : ∀ (l : List α) (k : Nat),
    (l.zipIdx k).map (fun x => f x.1) = l.map f
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, zipIdx_map_fst f l (k + 1)]

/-- The member of a numbered list that stands behind the members pre has the number of pre's
length, counted from the list's first number. -/
theorem zipIdx_at {α : Type} : ∀ (L : List α) (k : Nat) (pre : List (α × Nat)) (a : α × Nat)
    (rest : List (α × Nat)), L.zipIdx k = pre ++ a :: rest → a.2 = k + pre.length
  | [], k, pre, a, rest, h => by simp at h
  | x :: L, k, [], a, rest, h => by
    rw [List.zipIdx_cons, List.nil_append] at h
    rw [← (List.cons.inj h).1]
    rfl
  | x :: L, k, b :: pre, a, rest, h => by
    rw [List.zipIdx_cons, List.cons_append] at h
    rw [zipIdx_at L (k + 1) pre a rest (List.cons.inj h).2, List.length_cons]
    omega

/-- Two lists of one length, each with one member more, joined member by member. -/
theorem zipWith_snoc {α β γ : Type} (f : α → β → γ) : ∀ (as : List α) (bs : List β) (a : α)
    (b : β), as.length = bs.length →
    List.zipWith f (as ++ [a]) (bs ++ [b]) = List.zipWith f as bs ++ [f a b]
  | [], [], a, b, _ => rfl
  | x :: as, y :: bs, a, b, h => by
    rw [List.cons_append, List.cons_append, List.zipWith_cons_cons, List.zipWith_cons_cons,
      zipWith_snoc f as bs a b (by simpa using h), List.cons_append]
  | [], y :: bs, a, b, h => by simp at h
  | x :: as, [], a, b, h => by simp at h

/-- A list whose images end in k ends in a member with the image k. -/
theorem snoc_of_map {α β : Type} (g : α → β) : ∀ (l : List α) (K : List β) (k : β),
    l.map g = K ++ [k] → ∃ as a, l = as ++ [a] ∧ as.map g = K ∧ g a = k
  | [], K, k, h => by simp at h
  | x :: t, [], k, h => by
    rw [List.map_cons, List.nil_append] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    cases t with
    | nil => exact ⟨[], x, rfl, rfl, h1⟩
    | cons y t' => cases h2
  | x :: t, b :: K, k, h => by
    rw [List.map_cons, List.cons_append] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    obtain ⟨as, a, e1, e2, e3⟩ := snoc_of_map g t K k h2
    exact ⟨x :: as, a, by rw [e1, List.cons_append], by rw [List.map_cons, h1, e2], e3⟩

/-- The images of an array with one member more. -/
theorem map_push {α β : Type} (g : α → β) (s : Array α) (a : α) :
    (s.push a).toList.map g = s.toList.map g ++ [g a] := by
  rw [Array.toList_push, List.map_append]
  rfl

/-! ## The function that lists the links -/

/-- The kinds of the links before the head's, for n groups of layers: for each group a link of kind
0, followed by a link of kind 1 if the proof covers attention and there is a plan for the group. -/
def kindsL (p4 : Bool) (A : Array SubPlanH) : Nat → List Nat
  | 0 => []
  | n + 1 => kindsL p4 A n ++ (0 :: if p4 = true ∧ (A[n]?).isSome = true then [1] else [])

/-- **The list of links ends in the head's link, of kind 2**, and the kinds before it are
kindsL. -/
theorem listLinksH_kinds {NGr : Nat} {p4 : Bool} {G A : Array SubPlanH} {H : SubPlanH}
    {ls : Array LinkH} (h : Model.Stages.listLinksH NGr p4 G A H = .ok ls) :
    ∃ pre : Array LinkH, ls = pre.push (H.link "H" (1 + NGr) 2 0 true) ∧
      pre.toList.map (·.kind) = kindsL p4 A G.size := by
  unfold Model.Stages.listLinksH at h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨pre, hr, h⟩ := ok_of_bind h
  refine ⟨pre, (Except.ok.inj h).symm, ?_⟩
  have K : pre.toList.map (·.kind) = kindsL p4 A G.toList.zipIdx.length := by
    refine forIn_keeps _ G.toList.zipIdx
      (fun pr (s : Array LinkH) => s.toList.map (·.kind) = kindsL p4 A pr.length) ?_
      G.toList.zipIdx [] _ _ rfl rfl hr
    intro pr a rest e s s' hI0 hs
    have hI : s.toList.map (·.kind) = kindsL p4 A pr.length := hI0
    obtain ⟨sp, g⟩ := a
    have hg : g = pr.length := by
      have k := zipIdx_at _ _ _ _ _ e
      simpa using k
    have hlen : (pr ++ [(sp, g)]).length = pr.length + 1 := by
      rw [List.length_append]
      rfl
    have hK : kindsL p4 A (pr.length + 1) = kindsL p4 A pr.length ++
        (0 :: if p4 = true ∧ (A[pr.length]?).isSome = true then [1] else []) := rfl
    dsimp only at hs
    by_cases h4 : p4 = true
    · rw [if_pos h4] at hs
      cases hA : A[g]? with
      | some a2 =>
        rw [hA] at hs
        refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
        show ((s.push _).push _).toList.map (·.kind) = kindsL p4 A (pr ++ [(sp, g)]).length
        rw [hlen, hK, map_push, map_push, hI, if_pos ⟨h4, by rw [← hg, hA]; rfl⟩,
          List.append_assoc]
        rfl
      | none =>
        rw [hA] at hs
        refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
        show (s.push _).toList.map (·.kind) = kindsL p4 A (pr ++ [(sp, g)]).length
        rw [hlen, hK, map_push, hI, if_neg (fun c => by
          have c2 := c.2
          rw [← hg, hA] at c2
          cases c2)]
        rfl
    · rw [if_neg h4] at hs
      refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
      show (s.push _).toList.map (·.kind) = kindsL p4 A (pr ++ [(sp, g)]).length
      rw [hlen, hK, map_push, hI, if_neg (fun c => h4 c.1)]
      rfl
  rw [List.length_zipIdx, Array.length_toList] at K
  exact K

/-! ## The public tests on the links -/

/-- The declarations hand the links on in the same order, each with one field filled: whatever does
not read that field is kept. g: any function of a link that does not read the field arrayOf. -/
theorem declareLinks_keeps {β : Type} (g : LinkH → β)
    (hg : ∀ (X : LinkH) (a : Array (Nat × String)), g { X with arrayOf := a } = g X)
    {links : Array LinkH} {NGr : Nat} {p4 : Bool} {r : Array LinkH × Array FrameLink}
    (h : Model.Stages.declareLinks links NGr p4 = .ok r) :
    r.1.toList.map g = links.toList.map g := by
  unfold Model.Stages.declareLinks at h
  obtain ⟨st, hr, h⟩ := ok_of_bind h
  obtain ⟨declared, named⟩ := st
  have e : (named, declared) = r := Except.ok.inj h
  rw [← e]
  show named.toList.map g = _
  have K : named.toList.map g = links.toList.zipIdx.map (fun x => g x.1) := by
    refine forIn_keeps _ links.toList.zipIdx
      (fun pr (s : MProd (Array FrameLink) (Array LinkH)) =>
        s.snd.toList.map g = pr.map (fun x => g x.1)) ?_
      links.toList.zipIdx [] _ _ rfl rfl hr
    intro pr a rest e s s' hI0 hs
    have hI : s.snd.toList.map g = pr.map (fun x => g x.1) := hI0
    obtain ⟨X, l⟩ := a
    obtain ⟨d, -, hs⟩ := ok_of_bind hs
    obtain ⟨s2, -, hs⟩ := ok_of_bind hs
    obtain ⟨-, hs⟩ := ok_of_jp hs
    refine ⟨_, (Except.ok.inj hs).symm, ?_⟩
    show (s.snd.push { X with arrayOf := s2.1 }).toList.map g =
      (pr ++ [(X, l)]).map (fun x => g x.1)
    rw [map_push, hI, List.map_append, hg]
    rfl
  rw [K]
  exact zipIdx_map_fst g links.toList 0

/-- The links as built are the links that were given, in the same order, but for the field
arrayOf. -/
theorem buildLinksH_keeps {β : Type} (g : LinkH → β)
    (hg : ∀ (X : LinkH) (a : Array (Nat × String)), g { X with arrayOf := a } = g X)
    {links : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : Model.WsLay}
    {p : Params.First} {B : Model.Stages.LinksH}
    (h : Model.Stages.buildLinksH links NGr p4 wsLay p = .ok B) :
    B.links.toList.map g = links.toList.map g := by
  unfold Model.Stages.buildLinksH at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨⟨links', declared⟩, hd, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  cases h
  exact declareLinks_keeps g hg hd

/-! ## The list that the stage request runs -/

/-- **The joined list ends in a link of kind 2 whose routine is the head's**, for the request's
covered positions, and whose planned state and list of arrays are those of the head's plan. built:
the links as built; ls: the links made for the request. -/
theorem links_end {X : Model.Verify.Public} {chains : Model.Verify.Chains}
    {built : Model.Stages.LinksH} {cov : Model.Head.Covered} {ls : Array LinkH}
    (hb : Model.Verify.builtOf X chains = .ok built) (hl : Model.Verify.linksOf X cov = .ok ls) :
    ∃ (Xs : List LinkH) (Xh : LinkH),
      built.links.zipWith (fun b l => { b with run := l.run }) ls = (Xs ++ [Xh]).toArray ∧
      Xh.kind = 2 ∧ Xh.run = (Model.Verify.headPlanOf X cov).run ∧ Xh.Fp = X.H.Fp ∧
      Xh.Tp = X.H.Tp := by
  unfold Model.Verify.builtOf at hb
  obtain ⟨ls0, hl0, hb⟩ := ok_of_bind hb
  unfold Model.Verify.linksOf at hl0 hl
  obtain ⟨pre0, e0, k0⟩ := listLinksH_kinds hl0
  obtain ⟨pre, e1, k1⟩ := listLinksH_kinds hl
  rw [Array.size_mapIdx] at k0 k1
  have kb := buildLinksH_keeps (fun Z : LinkH => (Z.kind, Z.Fp, Z.Tp)) (fun _ _ => rfl) hb
  rw [e0, map_push] at kb
  obtain ⟨Bs, B, eB, kB, k2⟩ :=
    snoc_of_map (fun Z : LinkH => (Z.kind, Z.Fp, Z.Tp)) built.links.toList _ _ kb
  have hlen : Bs.length = pre.toList.length := by
    have a0 := congrArg List.length kB
    have a1 := congrArg List.length k0
    have a2 := congrArg List.length k1
    rw [List.length_map, List.length_map] at a0
    rw [List.length_map] at a1 a2
    rw [a0, a1, a2]
  have hz : (built.links.zipWith (fun b l => { b with run := l.run }) ls).toList =
      List.zipWith (fun (b l : LinkH) => { b with run := l.run }) Bs pre.toList ++
        [{ B with
          run := ((Model.Verify.headPlanOf X cov).link "H" (1 + X.NGr) 2 0 true).run }] := by
    rw [Array.toList_zipWith, eB, e1, Array.toList_push, zipWith_snoc _ _ _ _ _ hlen]
  refine ⟨List.zipWith (fun (b l : LinkH) => { b with run := l.run }) Bs pre.toList,
    { B with run := ((Model.Verify.headPlanOf X cov).link "H" (1 + X.NGr) 2 0 true).run },
    ?_, congrArg (fun t => t.1) k2, rfl, congrArg (fun t => t.2.1) k2,
    congrArg (fun t => t.2.2) k2⟩
  rw [← hz]

end OnBytes.TieK
