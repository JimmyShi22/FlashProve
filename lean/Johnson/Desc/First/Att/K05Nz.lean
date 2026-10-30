-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Nz.lean: the premise on the view BetasNz (Att/K5Data.lean), from the
general step's own
test. Block.lean's roundsFit asks drawsMarkedNonzeroHaveNonzeroWords: an element that a round's entry counts as drawn "never 0"
is not the
triple (0, 0, 0).

Main names:
  `nzE`, `NzF`, `nzF_of_fit`: the test by the entry; over lists; roundsFit gives it over the kind's
    entries.
  `Good`: any property of a triple of words, a parameter ("each word is below the prime" is what it
    is for).
    `RawNz Good b`: b is made of a drawn triple that is Good and other than (0, 0, 0).
  `parts_nz`: in a masked sumcheck's rounds the element drawn in the round of the further variable
    is RawNz.
  `Nz`; `take_nz`, `batch_nz`, `close_nz`, `sum_nz`, `takes_nz`, `units_nz`: verb by verb.
  `HeardNz`, `hear_nz`: where the hearing returns on rounds that pass roundsFit, the last challenge
    of each of
    the eight records is RawNz.
  `ReadsNz Good ρ`: the reading takes a Good triple other than (0, 0, 0) to an element other than 0.
  `readsNz_gl`: ReadsNz holds at the library's reading Reading.gl for Good := the format's own test
    okE (all three
    words are below the prime), by the library's toE_inj.
  `betas_nz`: roundsFit (rounds p) rs, the hearing's return, every drawn triple of rs is Good,
    ReadsNz Good ρ and
    Said give BetasNz ρ L.

Limits. drawsMarkedNonzeroHaveNonzeroWords tests the raw triple. A reading counts a word that is not below the prime as its
residue, so the
triple (p, 0, 0) passes drawsMarkedNonzeroHaveNonzeroWords and reads as 0: BetasNz follows only where every drawn triple is Good
for a Good at
which ReadsNz holds. Both are premises of betas_nz. readsNz_gl gives the second at Reading.gl. The
first, that every drawn
word is below the prime, is the general fold's test, not this kind's; it is not shown in this file
or in what it
imports.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (PscH)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)

/-- The general step's test on «never 0», by the entry. -/
def nzE (e : Fmt.Entry) (r : Fmt.RoundView) : Bool := drawsMarkedNonzeroHaveNonzeroWords { entry := e } r

/-- A triple of words, as a round's record holds a drawn element. -/
abbrev Tri : Type := UInt64 × UInt64 × UInt64

variable (Good : Tri → Prop)

/-- Entry for entry: the step's test on «never 0»; and every drawn triple is Good. -/
def NzF : List Fmt.Entry → List Fmt.RoundView → Prop
  | [], [] => True
  | e :: es, r :: rs => (nzE e r = true ∧ ∀ x ∈ r.drawn.elems, Good x) ∧ NzF es rs
  | _, _ => False

theorem nzF_of_fit : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), roundsFit ds rs = true →
    (∀ r ∈ rs, ∀ x ∈ r.drawn.elems, Good x) → NzF Good (ds.map (·.entry)) rs
  | [], [], _, _ => trivial
  | d :: ds, r :: rs, h, hg => by
    simp only [roundsFit, Bool.and_eq_true] at h
    exact ⟨⟨h.1.2, hg r (List.mem_cons_self ..)⟩, nzF_of_fit ds rs h.2 fun r' hr => hg r' (List.mem_cons_of_mem _ hr)⟩
  | [], _ :: _, h, _ => by simp [roundsFit] at h
  | _ :: _, [], h, _ => by simp [roundsFit] at h

variable {Good}

theorem NzF.map {g : Fmt.Entry → Fmt.Entry} (hg : ∀ e r, nzE (g e) r = nzE e r) :
    ∀ {es : List Fmt.Entry} {rs : List Fmt.RoundView}, NzF Good (es.map g) rs → NzF Good es rs
  | [], [], _ => trivial
  | e :: _, r :: _, ⟨⟨a, a'⟩, b⟩ => ⟨⟨(hg e r).symm.trans a, a'⟩, NzF.map hg b⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem NzF.split : ∀ {a b : List Fmt.Entry} {x y : List Fmt.RoundView}, a.length = x.length → NzF Good (a ++ b) (x ++ y) →
    NzF Good a x ∧ NzF Good b y
  | [], _, [], _, _, h => ⟨trivial, h⟩
  | _ :: _, _, _ :: _, _, hl, ⟨h1, h2⟩ =>
    let ⟨c1, c2⟩ := NzF.split (by simpa using hl) h2
    ⟨⟨h1, c1⟩, c2⟩
  | [], _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _, [], _, hl, _ => by simp at hl

variable (Good)

/-- Made of a drawn triple that is Good and other than (0, 0, 0). -/
def RawNz (b : E) : Prop := ∃ x : Tri, b = E.ofTriple x ∧ x ≠ (0, 0, 0) ∧ Good x

variable {Good}

theorem raw_of_round {dY : ℕ} {rY : Fmt.RoundView} {sentY : List E} {beta : E}
    (h : nzE (MaskedSum.entry "PSC Y" dY 1 1) rY = true) (hg : ∀ x ∈ rY.drawn.elems, Good x)
    (hr : IsRound rY (sentY, some [beta])) : RawNz Good beta := by
  have hd : [beta] = rY.drawn.elems.map E.ofTriple := hr.2 _ rfl
  rcases he : rY.drawn.elems with _ | ⟨x, _ | ⟨y, l⟩⟩
  · rw [he] at hd; simp at hd
  · rw [he] at hd
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hd
    refine ⟨x, hd, fun h0 => ?_, hg x (by rw [he]; exact List.mem_cons_self ..)⟩
    have hk : Fmt.kindOf "PSC Y" = some .elems := by decide
    unfold nzE drawsMarkedNonzeroHaveNonzeroWords at h
    simp only [MaskedSum.entry, hk, Option.any_some, he] at h
    subst h0
    simp [Fmt.dsElems] at h
  · rw [he] at hd; simp at hd

theorem mid_nz {eY eV : Fmt.Entry} {y z : RoundH} {g : Var → Fmt.Entry} {f : List E × E → RoundH} :
    ∀ (vs : List Var) (rs : List (List E × E)) (used : List Fmt.RoundView), rs.length = vs.length →
      NzF Good (vs.map g ++ [eY, eV]) used → RoundsAre (rs.map f ++ [y, z]) used →
      ∃ rY, (nzE eY rY = true ∧ ∀ x ∈ rY.drawn.elems, Good x) ∧ IsRound rY y := by
  intro vs
  induction vs with
  | nil =>
    intro rs used hl a b
    have e0 : rs = [] := List.eq_nil_of_length_eq_zero hl
    subst e0
    rcases used with _ | ⟨rY, used⟩
    · exact a.elim
    · exact ⟨rY, a.1, b.1⟩
  | cons v vs ih =>
    intro rs used hl a b
    rcases rs with _ | ⟨x, rs⟩
    · simp at hl
    rcases used with _ | ⟨r, used⟩
    · exact a.elim
    · exact ih rs used (by simpa using hl) a.2 b.2

/-- In a masked sumcheck's rounds the element drawn in the round of the further variable is RawNz.
-/
theorem parts_nz {lead : ℕ} {vs : List Var} {e : Ends} {pre : List E} {mu eps : E} {rs : List (List E × E)}
    {sentY : List E} {beta : E} {v : List E} {used : List Fmt.RoundView} (hl : rs.length = vs.length)
    (a : NzF Good (MaskedSum.entries ⟨lead, vs, some e⟩) used)
    (b : RoundsAre (partsRounds pre mu eps rs sentY beta v) used) : RawNz Good beta := by
  rcases used with _ | ⟨r0, used⟩
  · exact a.elim
  obtain ⟨rY, ⟨c1, c1'⟩, c2⟩ := mid_nz vs rs used hl a.2 b.2
  exact raw_of_round c1 c1' c2

theorem roundsAre_length : ∀ {hs : List RoundH} {rs : List Fmt.RoundView}, RoundsAre hs rs → hs.length = rs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg (· + 1) (roundsAre_length h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-! ## Verb by verb -/

variable (Good)

/-- The rounds left pass, against the entries of the stages left. -/
def Nz (st : List Stage) (s : St) : Prop := NzF Good (entriesOf s.2.2 st) s.2.1

variable {Good}

theorem take_nz {n j : ℕ} {l : List Stage} {s s' : St} (h : take n s = some (j, s'))
    (a : Nz Good (.scalars n :: l) s) : Nz Good l s' := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, e1, e2, _⟩ := take_spec h
  subst e1 e2
  exact a

theorem batch_nz {rows : ℕ} {w : Array E} {l : List Stage} {s s' : St} (h : batch rows s = some (w, s'))
    (a : Nz Good (.batch rows :: l) s) : Nz Good l s' := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, e2, r, x, e3, _⟩ := batch_spec h
  subst e2 e3
  exact a.2

theorem close_nz {n : ℕ} {d : List E} {l : List Stage} {s s' : St} (h : close n s = some (d, s'))
    (a : Nz Good (.point n :: l) s) : Nz Good l s' := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, e2, r, e3, _⟩ := close_spec h
  subst e2 e3
  exact a.2

theorem sum_nz {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {k : ℕ} {l : List Stage} {s s' : St}
    (h : sum C (.sum vs e) s = some (hh, s')) (ha : At s k) (a : Nz Good (.sum vs e :: l) s) :
    RawNz Good (hh.r.getLastD zeroE) ∧ Nz Good l s' := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨hz, _, pre, ho⟩ := ha
  obtain ⟨e0, H, used, e1, sd⟩ := sum_said h hz ho
  subst e0 e1
  have hlen : H.rs.length = vs.length := by simpa using congrArg List.length sd.lens
  have hul : (MaskedSum.entries ⟨lead, vs, some e⟩).length = used.length := by
    rw [← roundsAre_length sd.rounds]
    simp [MaskedSum.entries, partsRounds, hlen]
  obtain ⟨c1, c2⟩ := NzF.split hul a
  refine ⟨?_, c2⟩
  rw [sd.r]
  have : (H.rs.map (·.2) ++ [H.beta]).getLastD zeroE = H.beta := by simp
  rw [this]
  exact parts_nz hlen c1 sd.rounds

theorem takes_nz {l : List Stage} : ∀ (n : ℕ) (js : List ℕ) (s s' : St), TakesRan 3 n js s s' →
    Nz Good (List.replicate n (.scalars 3) ++ l) s → Nz Good l s'
  | 0, [], s, s', h, a => by
    have e : s' = s := h
    subst e
    exact a
  | n + 1, _ :: js, s, s', ⟨s1, h1, h2⟩, a => takes_nz n js s1 s' h2 (take_nz h1 a)
  | 0, _ :: _, _, _, h, _ => h.elim
  | _ + 1, [], _, _, h, _ => h.elim

theorem units_nz {l : List Stage} : ∀ (us : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (s s' : St) (k : ℕ),
    UnitsRan us os s s' → At s k → Nz Good ((us.flatMap fun u => [.scalars 7, products u.1 u.2]) ++ l) s →
    (∀ o ∈ os, RawNz Good (o.2.r.getLastD zeroE)) ∧ Nz Good l s'
  | [], [], s, s', _, h, _, a => by
    have e : s' = s := h
    subst e
    exact ⟨fun _ ho => (by cases ho), a⟩
  | u :: us, o :: os, s, s', k, ⟨s2, ⟨s1, h1, h2⟩, h3⟩, ha, a => by
    have a1 := (take_at h1 ha).2
    obtain ⟨c1, c2⟩ := sum_nz h2 a1 (take_nz h1 a)
    obtain ⟨d1, d2⟩ := units_nz us os s2 s' _ h3 (sum_at h2 a1).2.2 c2
    refine ⟨fun o' ho => ?_, d2⟩
    rcases List.mem_cons.1 ho with rfl | ho
    · exact c1
    · exact d1 o' ho
  | [], _ :: _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, h, _, _ => h.elim

theorem nz_assoc {a b c : List Stage} {s : St} (h : Nz Good ((a ++ b) ++ c) s) : Nz Good (a ++ (b ++ c)) s := by
  rwa [List.append_assoc] at h

/-! ## The whole -/

variable (Good)

/-- The last challenge of each of the hearing's records is RawNz. -/
structure HeardNz (h : Heard) : Prop where
  units : ∀ o ∈ h.scores.toList, RawNz Good (o.2.r.getLastD zeroE)
  bE : RawNz Good (h.division.r.getLastD zeroE)
  bM : RawNz Good (h.below.r.getLastD zeroE)
  bVD : RawNz Good (h.on.r.getLastD zeroE)
  bF : RawNz Good (h.atIndex.r.getLastD zeroE)
  bD : RawNz Good (h.key.r.getLastD zeroE)
  bH : RawNz Good (h.cells.r.getLastD zeroE)

/-- **The words' test, named**: the reading takes a Good triple other than (0, 0, 0) to an element
other than 0. -/
def ReadsNz {K : Type} [Field K] (ρ : Reading K) : Prop :=
  ∀ x : Tri, Good x → x ≠ (0, 0, 0) → ρ.val (E.ofTriple x) ≠ 0

variable {Good}

theorem hear_nz (p : Par) {F : Fork} {rs : List Fmt.RoundView} {h : Heard} {s' : St}
    (hh : hear p.own (F, rs, 0) = some (h, s')) (hz : Sized F) (hf : roundsFit (rounds p) rs = true)
    (hg : ∀ r ∈ rs, ∀ x ∈ r.drawn.elems, Good x) : HeardNz Good h := by
  have n0 : Nz Good (script p.own) (F, rs, 0) := by
    have := nzF_of_fit Good (rounds p) rs hf hg
    unfold rounds at this
    rw [List.map_map] at this
    exact NzF.map (g := fun e => if e.drawE == 0 then e else { e with work := p.work }) (fun e r => by
      show nzE (if e.drawE == 0 then e else { e with work := p.work }) r = _
      split <;> rfl) this
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ha, hb, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, _, h10, h11, h12, h13, h14, h15, h16⟩ := (hear_ran hh).ran
  have a0 : At (F, rs, 0) F.next := ⟨hz, rfl, [], open_zero _⟩
  obtain ⟨_, aa⟩ := takes_at _ _ _ _ _ ha a0
  obtain ⟨_, ab⟩ := units_at _ _ _ _ _ hb aa
  obtain ⟨_, a1⟩ := take_at h1 ab
  obtain ⟨_, a2⟩ := take_at h2 a1
  obtain ⟨_, a3⟩ := take_at h3 a2
  obtain ⟨_, _, a4⟩ := sum_at h4 a3
  have a5 := batch_at h5 a4
  obtain ⟨_, a6⟩ := take_at h6 a5
  obtain ⟨_, _, a7⟩ := sum_at h7 a6
  obtain ⟨_, _, a8⟩ := sum_at h8 a7
  have a9 := close_at h9 a8
  obtain ⟨_, a10⟩ := take_at h10 a9
  have a11 := batch_at h11 a10
  obtain ⟨_, _, a12⟩ := sum_at h12 a11
  have a13 := batch_at h13 a12
  obtain ⟨_, _, a14⟩ := sum_at h14 a13
  have a15 := batch_at h15 a14
  have na := takes_nz _ _ _ _ ha (nz_assoc n0)
  obtain ⟨ru, nb⟩ := units_nz _ _ _ _ _ hb aa na
  obtain ⟨rE, n4⟩ := sum_nz h4 a3 (take_nz h3 (take_nz h2 (take_nz h1 nb)))
  obtain ⟨rM, n7⟩ := sum_nz h7 a6 (take_nz h6 (batch_nz h5 n4))
  obtain ⟨rVD, n8⟩ := sum_nz h8 a7 n7
  obtain ⟨rF, n12⟩ := sum_nz h12 a11 (batch_nz h11 (take_nz h10 (close_nz h9 n8)))
  obtain ⟨rD, n14⟩ := sum_nz h14 a13 (batch_nz h13 n12)
  obtain ⟨rH, _⟩ := sum_nz h16 a15 (batch_nz h15 n14)
  exact ⟨ru, rE, rM, rVD, rF, rD, rH⟩

/-- A sumcheck's beta is the last challenge of its record. -/
theorem beta_last {C : Aff} {st : Stage} {pre : List E} {H : PscH} {hh : MaskedSum.Heard} {G : Fork}
    (h : SumAt C st pre H hh G) : hh.r.getLastD zeroE = H.beta := by
  obtain ⟨vs, e, F, G0, used, _, sd, _⟩ := h
  rw [sd.r]
  simp

theorem units_beta {K : Type} [Field K] {ρ : Reading K} (hρ : ReadsNz Good ρ) {G : Fork} :
    ∀ (ps : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (pre : List E) (l : List (List E × PscH)),
      UnitsAt ps os pre l G → (∀ o ∈ os, RawNz Good (o.2.r.getLastD zeroE)) → ∀ u ∈ l, ρ.val u.2.beta ≠ 0
  | [], [], _, [], _, _ => fun _ hu => by cases hu
  | _ :: ps, o :: os, _, (_, H) :: l, ⟨_, _, a3, _, a5⟩, hn => fun u hu => by
    rcases List.mem_cons.1 hu with rfl | hu
    · obtain ⟨x, e1, e2, e3⟩ := hn o (List.mem_cons_self ..)
      rw [beta_last a3] at e1
      show ρ.val H.beta ≠ 0
      rw [e1]
      exact hρ x e3 e2
    · exact units_beta hρ ps os [] l a5 (fun o' ho => hn o' (List.mem_cons_of_mem _ ho)) u hu
  | [], [], _, _ :: _, h, _ => h.elim
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim
  | _ :: _, _ :: _, _, [], h, _ => h.elim

/-- **BetasNz from the general step's test**, with the words' test named. -/
theorem betas_nz {K : Type} [Field K] {ρ : Reading K} (p : Par) {F G G' : Fork} {rs rs' : List Fmt.RoundView} {lead : ℕ}
    {h : Heard} {L : Lists} (hh : hear p.own (F, rs, 0) = some (h, G, rs', lead)) (hz : Sized F)
    (hf : roundsFit (rounds p) rs = true) (hg : ∀ r ∈ rs, ∀ x ∈ r.drawn.elems, Good x) (hρ : ReadsNz Good ρ)
    (hs : Said p.own h G' L) : BetasNz ρ L := by
  have hn := hear_nz p hh hz hf hg
  have one : ∀ {C : Aff} {st : Stage} {pre : List E} {H : PscH} {hx : MaskedSum.Heard},
      SumAt C st pre H hx G' → RawNz Good (hx.r.getLastD zeroE) → ρ.val H.beta ≠ 0 := by
    intro C st pre H hx a ⟨x, e1, e2, e3⟩
    rw [beta_last a] at e1
    rw [e1]
    exact hρ x e3 e2
  exact ⟨units_beta hρ _ _ _ _ hs.units hn.units, one hs.sE hn.bE, one hs.sM hn.bM, one hs.sVD hn.bVD,
    one hs.sF hn.bF, one hs.sD hn.bD, one hs.sH hn.bH⟩

/-- **The words' test at the reading that runs**: at the library's reading in its extension field,
and Good := all three words
are below the prime (the format's own test okE): by the library's toE_inj. -/
theorem readsNz_gl : ReadsNz (fun x : Tri => Fmt.Fld.two.okE x = true) Reading.gl := fun x hx hne h0 =>
  hne (Slice.toE_inj x Fmt.Fld.zeroE hx (by decide) (Eq.trans h0 Slice.toE_zeroE.symm))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.readsNz_gl
#print axioms VerifiableInference.Desc.First.Att.P.hear_nz
#print axioms VerifiableInference.Desc.First.Att.P.betas_nz
