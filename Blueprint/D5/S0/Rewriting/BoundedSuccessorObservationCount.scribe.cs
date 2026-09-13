using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;

internal sealed class BoundedSuccessorObservationCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded Successor Observation Count",
        H("Bounded Successor Observation Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boundedsuccessorobservationcount-bounded-successor-trajectory"),
                DeclarationHandle.Create("D5/S0/Rewriting/BoundedSuccessorObservationCount.bounded_successor_trajectory"),
                H("The bounded successor reaches failure at its arithmetic boundary"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Iterating the strict successor from a state n yields n+t while the bound B is not exceeded, "
                    + "and thereafter yields the absorbing failure state. For a starting state n at most B, the "
                    + "first failure transition therefore occurs after B minus n plus one steps."))),
                DescribeRole.Theorem))));
}
