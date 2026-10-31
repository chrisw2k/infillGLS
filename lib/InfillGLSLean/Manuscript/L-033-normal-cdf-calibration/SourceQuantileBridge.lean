module

public import «L-033-normal-cdf-calibration».Explore
public import ManuscriptSpecification

namespace InfillGLSLean.ManuscriptSpecification.L033

open MeasureTheory ProbabilityTheory

/- This derived source-quantile bridge is consumed by external coverage
integration modules.  Exporting it changes no proposition or premise. -/
public section

/-- The source's stored one-sided normal-quantile calibration entails the
two-sided interval mass required by `InfillGLSLean.Coverage`.  This is a
derived analytic bridge, not an added hypothesis of Proposition 3. -/
theorem sourceQuantile_interval_toNNReal {α : ℝ} (z : StandardNormalQuantile α) :
    (gaussianReal 0 1 (Set.Icc (-z.value) z.value)).toNNReal =
      (1 - α).toNNReal :=
  InfillGLSLean.NormalCDFCalibration.standardNormal_interval_toNNReal_of_quantile
    z.alpha_pos z.alpha_lt_one z.cdf_value

end

end InfillGLSLean.ManuscriptSpecification.L033
