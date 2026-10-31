module

import ManuscriptEndpoints

/-!
# Import-boundary check for theorem endpoints

This file imports only the public endpoint aggregator. It verifies that the
three main propositions remain available with their unchanged targets across a
package boundary.
-/

namespace InfillGLSLean.ManuscriptSpecification.ExternalConsumer

#check L029.manuscriptConsistency_complete
#check L055.manuscriptNormality_complete
#check L063.manuscriptVariance_complete
#check L064.residualScale_rate_decomposition
#check L065.conditionalMean_bias_tendsto

#print axioms L029.manuscriptConsistency_complete
#print axioms L055.manuscriptNormality_complete
#print axioms L063.manuscriptVariance_complete
#print axioms L064.residualScale_rate_decomposition
#print axioms L065.conditionalMean_bias_tendsto

end InfillGLSLean.ManuscriptSpecification.ExternalConsumer
