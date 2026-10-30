-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeRowZero.lean: AT THE FILLING OF THE LAST CHAIN'S TABLE'S PROMISE BY
`shapeAt`, READ OFF THE TWO CHAINS' OWN RECORDS: WHAT ROW 0 (K14's second part) ASKS OF THE PROMISE
AT BORDER 0. One definition; statements and proofs.

Why. Row 0 of the table of the last chain's joints is typed and joined in another file over letters
(`RowZeroAtWords`, Johnson/Desc/Third/Law/Row0AtWords.lean). Seven of its fields are
book-keeping on public records inside the promise: at border 0: started, weights, names, placed,
tenant; shape: the promise's test at border 1 behind the block's yes; and, at border 1, codes. Here
each is had from the test `shapeAt` (Johnson/Desc/Last/ShapeAt.lean), at a closed filling. This file
does not import that file: each statement has the body of the field that it pays, so that
the field is one call.

Main names (namespace `VerifiableInference.Desc.Last`).
  **`fillZ p R fs`** := `fillAt p R (fun q => firstOfS (fs q)) fun d => (Desc.K14.ended d).map
    sharedOfEnd`: what was handed is what `firstOfS` takes of the first chain's last record `fs q`;
    the shared chain's end is what `sharedOfEnd` takes of K14's own end (both:
    Johnson/Desc/Third/Border.lean). fs : P × S₁ → First.S IS A LETTER: how the first chain's last
    record is read off the table's first part.
  `shape_of_fillZ`: inside the promise at border k: something was handed, K14 has ended, `shapeAt`
    says yes. `firstOfS_parts`: what `firstOfS` takes has the record's own statement, book and
    pending rows.
  **`started_fillZ`**: K14 has ended at some e and `startAtEnds p … (fs …) e = .ok` the record in
    front. `weights_fillZ`: every weight of every pending row is well-formed. `names_fillZ`.
    `placed_fillZ`: every place of the first chain's last book names a tree that is there.
    `tenant_fillZ`: in the shared chain's book Omega is part 0 of its tree: stated at `sharedOfEnd
    e`.
  **`shape_fillZ`**: behind a yes of K14's second part at the record in front, `(fillZ p R fs).shape
    1` says yes at the record behind: by `step_zero` (Johnson/Desc/Last/ShapeGives.lean), which has
    no debt.
  `codes_fillZ`: inside the promise at border 1 the record's table of codes is the plan's `p.codes`
    (the later field `codes` of Johnson/Desc/Third/Law/Row0AtFillings.lean, at cs := p.codes).

Every "there is", walked. f, e (`shape_of_fillZ`): tied by `firstOfS … = some f` and `ended … = some
e`: at most one each. e (`started_fillZ`, `tenant_fillZ`): likewise. rs, gs (`shape_fillZ`'s
premise): the block's own yes.
Limits. (1) NO MEMBER: that some record lies inside the promise at border 0 at this filling is shown
nowhere: `shapeAt` has been evaluated at no record. All hold for nothing where the promise is empty;
it IS empty at a shape whose masks are not sent ahead (ShapeAt.lean, limit 2). (2) fs is a letter:
nothing says that it reads the right record. (3) `tenant_fillZ` speaks of `sharedOfEnd e`; that its
book and Omega's number are K14's last record's: `sharedOfEnd_ended` (Row0AtWords.lean). (4) Row 0's
other fields are not touched: the piece's form; the pins; what the fillings of the meaning are;
and `laid` (that the row (Eval) lies among the own group's open rows of the first chain's last
record): NO CLAUSE OF `shapeAt` SPEAKS OF IT. (5) THE DEBT MOVES TO THE DOOR. started, weights,
names, placed, tenant and codes are unfoldings of what `fillZ` lays INTO the promise: they would
stay proved whatever the block did. Whoever lays PL := `fillZ p R fs` owes each of them again where
the last chain is entered: that border 0's promise at `fillZ` follows from the shared chain's last
promise and the start's yes (the clause on `PL.shape 0` in `OnZero₃OfEnd₂`,
Johnson/Desc/Sound/BordersLastQ.lean): STATED, AND CUT INTO THREE CONDITIONS, IN
Johnson/Desc/Last/ShapeDoor.lean; what is proved of each: that file's head. `shape_fillZ` alone
spends the block's text. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeRows
import Johnson.Desc.Third.Border
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Book (placed_of_fits)
open _root_.Desc.K14 (St)
open _root_.Run.PQ (CK)

variable {P S₁ Wt : Type} {Fr : Frame} (N : NumbersS) (Mg : MeaningS St (P × S₁) Wt)
  (Pm : PromMeaning St) (Oc : P × S₁ → Strs → Prop) (p : P₁₄) (R : List Fmt.DeclaredRound)
  (fs : P × S₁ → First.S)

/-- **THE FILLING AT THE TWO CHAINS' OWN RECORDS**: what was handed is what `firstOfS` takes of the
first chain's last record; the shared chain's end is what `sharedOfEnd` takes of K14's own end. -/
def fillZ : PromMeaningL St S₃ (P × S₁) :=
  fillAt p R (fun q => firstOfS (fs q)) fun d => (_root_.Desc.K14.ended d).map sharedOfEnd

variable {N Mg Pm Oc p R fs}

/-- Inside the promise at border k: what was handed, K14's end, and the test's yes. -/
theorem shape_of_fillZ {k : ℕ} {a : ((P × S₁ × St) × S₃) × Fr.E.Str}
    (h : onQ₃ N Mg Pm (fillZ p R fs) Oc k a) :
    ∃ f e, firstOfS (fs (a.1.1.1, a.1.1.2.1)) = some f ∧
      _root_.Desc.K14.ended a.1.1.2.2 = some e ∧ shapeAt p R k f (sharedOfEnd e) a.1.2 = true := by
  obtain ⟨f, o, hf, ho, hs⟩ := shapeAt_of_onL N Mg Pm Oc p R _ _ h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 ho
  exact ⟨f, e, hf, he, hs⟩

/-- What `firstOfS` takes: the record's own statement, book and pending rows. -/
theorem firstOfS_parts {s : First.S} {f : FirstEnd₃} (h : firstOfS s = some f) :
    f.st = s.st ∧ f.book = s.book ∧ f.pending = s.rows := by
  obtain ⟨e, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, rfl, rfl⟩

/-- **started**: inside the promise at border 0 the record is the start's of what was handed. -/
theorem started_fillZ {a : ((P × S₁ × St) × S₃) × Fr.E.Str}
    (h : onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a) :
    ∃ e, _root_.Desc.K14.ended a.1.1.2.2 = some e ∧
      startAtEnds p a.1.1.1 (fs (a.1.1.1, a.1.1.2.1)) e = .ok a.1.2 := by
  obtain ⟨f, e, hf, he, hs⟩ := shape_of_fillZ h
  refine ⟨e, he, ?_⟩
  unfold startAtEnds start₃F
  rw [hf]
  exact (started_of_shape hs).1

/-- **weights**: the pending rows' weights are well-formed. -/
theorem weights_fillZ {a : ((P × S₁ × St) × S₃) × Fr.E.Str}
    (h : onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a) :
    ∀ r ∈ (fs (a.1.1.1, a.1.1.2.1)).rows, ∀ g ∈ r.g, g.ok = true := by
  obtain ⟨f, e, hf, _, hs⟩ := shape_of_fillZ h
  obtain ⟨r₀, hr₀, hg⟩ := (started_of_shape hs).2.1.weights
  intro r hr g hgr
  rw [← (firstOfS_parts hf).2.2, hr₀] at hr
  obtain rfl := List.mem_singleton.1 hr
  exact hg g hgr

/-- **names**: each message that an open row of the own group names is one of the statement's: its
number is below their count. -/
theorem names_fillZ {a : ((P × S₁ × St) × S₃) × Fr.E.Str}
    (h : onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a) :
    ∀ G, a.1.2.st.groups[a.1.2.loc.own]? = some G → ∀ r ∈ G.rows.toList, ∀ o ∈ r.oracles,
      o < a.1.2.st.oracles.size := by
  obtain ⟨_, _, _, _, hs⟩ := shape_of_fillZ h
  exact names_of (started_of_shape hs).2.2.1

/-- **placed**: every place of the first chain's last book names a tree that is there. -/
theorem placed_fillZ {a : ((P × S₁ × St) × S₃) × Fr.E.Str}
    (h : onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a) :
    ∀ (i : ℕ) (q : ℕ × ℕ), (fs (a.1.1.1, a.1.1.2.1)).book.place[i]? = some q →
      q.1 < (fs (a.1.1.1, a.1.1.2.1)).book.trees.size := by
  obtain ⟨f, _, hf, _, hs⟩ := shape_of_fillZ h
  have H := (started_of_shape hs).2.1.fits₁
  rw [(firstOfS_parts hf).2.1] at H
  exact fun i q hq => placed_of_fits H i q hq

/-- **tenant**: in the shared chain's book Omega is part 0 of its tree: at what `sharedOfEnd` takes
of K14's own end. -/
theorem tenant_fillZ {a : ((P × S₁ × St) × S₃) × Fr.E.Str}
    (h : onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a) :
    ∃ e, _root_.Desc.K14.ended a.1.1.2.2 = some e ∧
      ∀ q : ℕ × ℕ, (sharedOfEnd e).book.place[(sharedOfEnd e).omega]? = some q → q.2 = 0 := by
  obtain ⟨_, e, _, he, hs⟩ := shape_of_fillZ h
  exact ⟨e, he, (started_of_shape hs).2.1.tenant⟩

/-- **shape**: behind a yes of K14's second part the filling says yes at border 1. -/
theorem shape_fillZ {Cl₀ : Type} {a : ((P × S₁ × St) × S₃) × Fr.E.Str} {s' : S₃}
    (h : onQ₃ N Mg Pm (fillZ p R fs) Oc 0 a)
    (hy : ∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide a.1.2 rs gs = .ok s') :
    (fillZ p R fs).shape 1 (a.1.1.1, a.1.1.2.1) a.1.1.2.2 s' = true := by
  obtain ⟨f, e, hf, he, hs⟩ := shape_of_fillZ h
  obtain ⟨rs, gs, hd⟩ := hy
  exact fill_of_shapeAt p R _ _ hf (by rw [he]; rfl) (step_zero hs rs gs hd)

/-- **codes**: inside the promise at border 1 the record's table of codes is the plan's. -/
theorem codes_fillZ {b : ((P × S₁ × St) × S₃) × Fr.E.Str}
    (h : onQ₃ N Mg Pm (fillZ p R fs) Oc 1 b) : b.1.2.st.codes = p.codes := by
  obtain ⟨_, _, _, _, hs⟩ := shape_of_fillZ h
  obtain ⟨s₀, B⟩ := behindOk_of_one hs
  obtain ⟨_, _, _, _, L⟩ := B.laid
  obtain ⟨f, _, hst⟩ := Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨c1, _, e0⟩ := Law.start₃_inv _ _ _ _ hst
  rw [L.codes, e0]
  exact c1

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.codes_fillZ
#print axioms VerifiableInference.Desc.Last.shape_of_fillZ
#print axioms VerifiableInference.Desc.Last.firstOfS_parts
#print axioms VerifiableInference.Desc.Last.started_fillZ
#print axioms VerifiableInference.Desc.Last.weights_fillZ
#print axioms VerifiableInference.Desc.Last.names_fillZ
#print axioms VerifiableInference.Desc.Last.placed_fillZ
#print axioms VerifiableInference.Desc.Last.tenant_fillZ
#print axioms VerifiableInference.Desc.Last.shape_fillZ
