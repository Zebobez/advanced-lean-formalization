module

public import Mathlib

public section

/-!
# Chapter 106 — Structured Gap Estimation for Generalized Linear Frank–Wolfe

Extracted from manuscript/chapters/part-23/chapter-106-structured-frank-wolfe-gap-estimation.md.
Generated for leanprover/lean4:v4.35.0 and Mathlib ref v4.35.0.
Only complete top-level Lean commands are included. Interactive tactic fragments and diagnostic states remain in the manuscript.
-/

namespace Book.Chapters.Chapter106

-- Source Lean fence 1
def featureOne106 : ℚ := 1
def featureTwo106 : ℚ := 2

def componentOneDerivative106 (z : ℚ) : ℚ := z - 1
def componentTwoDerivative106 (z : ℚ) : ℚ := z + 1

def initialPoint106 : ℚ := 0
def pointAfterFirstStep106 : ℚ := 2 / 3

def initialTable106 : ℚ × ℚ := (0, 0)

def tableAfterFirstRefresh106 : ℚ × ℚ :=
  (componentOneDerivative106 (featureOne106 * initialPoint106) / 2,
    initialTable106.2)

def tableAfterSecondRefresh106 : ℚ × ℚ :=
  (tableAfterFirstRefresh106.1,
    componentTwoDerivative106 (featureTwo106 * pointAfterFirstStep106) / 2)

def aggregate106 (table : ℚ × ℚ) : ℚ :=
  featureOne106 * table.1 + featureTwo106 * table.2

def aggregateAfterFirstRefresh106 : ℚ :=
  aggregate106 initialTable106 +
    (tableAfterFirstRefresh106.1 - initialTable106.1) * featureOne106

def aggregateAfterSecondRefresh106 : ℚ :=
  aggregateAfterFirstRefresh106 +
    (tableAfterSecondRefresh106.2 - tableAfterFirstRefresh106.2) * featureTwo106

theorem aggregate_invariant_after_first_refresh :
    aggregate106 tableAfterFirstRefresh106 = aggregateAfterFirstRefresh106 := by
  norm_num [aggregate106, aggregateAfterFirstRefresh106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    featureOne106, featureTwo106, initialPoint106]

theorem aggregate_invariant_after_second_refresh :
    aggregate106 tableAfterSecondRefresh106 = aggregateAfterSecondRefresh106 := by
  norm_num [aggregate106, aggregateAfterSecondRefresh106,
    aggregateAfterFirstRefresh106, tableAfterSecondRefresh106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    componentTwoDerivative106, featureOne106, featureTwo106,
    initialPoint106, pointAfterFirstStep106]

def trueTableAtPoint106 : ℚ × ℚ :=
  (componentOneDerivative106 (featureOne106 * pointAfterFirstStep106) / 2,
    componentTwoDerivative106 (featureTwo106 * pointAfterFirstStep106) / 2)

def tableError106 : ℚ :=
  |tableAfterSecondRefresh106.1 - trueTableAtPoint106.1| +
    |tableAfterSecondRefresh106.2 - trueTableAtPoint106.2|

theorem stale_table_error_is_one_third : tableError106 = 1 / 3 := by
  norm_num [tableError106, tableAfterSecondRefresh106, trueTableAtPoint106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    componentTwoDerivative106, featureOne106, featureTwo106,
    initialPoint106, pointAfterFirstStep106]

def gradientGap106 (gradient : ℚ) : ℚ :=
  gradient * (pointAfterFirstStep106 + 1)

def cachedGradient106 : ℚ := aggregate106 tableAfterSecondRefresh106
def trueGradient106 : ℚ := aggregate106 trueTableAtPoint106

theorem cached_aggregate_is_eleven_sixths : cachedGradient106 = 11 / 6 := by
  norm_num [cachedGradient106, aggregate106, tableAfterSecondRefresh106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    componentTwoDerivative106, featureOne106, featureTwo106,
    initialPoint106, pointAfterFirstStep106]

theorem true_aggregate_is_thirteen_sixths : trueGradient106 = 13 / 6 := by
  norm_num [trueGradient106, aggregate106, trueTableAtPoint106,
    componentOneDerivative106, componentTwoDerivative106,
    featureOne106, featureTwo106, pointAfterFirstStep106]

theorem observed_gap_difference_is_five_ninths :
    |gradientGap106 trueGradient106 - gradientGap106 cachedGradient106| = 5 / 9 := by
  norm_num [gradientGap106, trueGradient106, cachedGradient106,
    aggregate106, trueTableAtPoint106, tableAfterSecondRefresh106,
    tableAfterFirstRefresh106, initialTable106, componentOneDerivative106,
    componentTwoDerivative106, featureOne106, featureTwo106,
    initialPoint106, pointAfterFirstStep106]

theorem gap_error_is_bounded_by_data_diameter_times_table_error :
    |gradientGap106 trueGradient106 - gradientGap106 cachedGradient106| ≤
      4 * tableError106 := by
  norm_num [gradientGap106, trueGradient106, cachedGradient106,
    aggregate106, tableError106, trueTableAtPoint106,
    tableAfterSecondRefresh106, tableAfterFirstRefresh106,
    initialTable106, componentOneDerivative106, componentTwoDerivative106,
    featureOne106, featureTwo106, initialPoint106, pointAfterFirstStep106]

end Book.Chapters.Chapter106
