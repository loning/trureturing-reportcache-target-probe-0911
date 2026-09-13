using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class CapacityBoxOneBitRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Boolean hypercube cannot return to a different diagonal after two consecutive edges use the same bit.",
        H("Capacity Box One-Bit Rigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("same-colour-adjacent-edges-force-diagonal"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.same_colour_adjacent_edges_force_diagonal"),
            H("Same-colour adjacent edges force the diagonal"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For Boolean words indexed by a finite bit set, if the supports of the changes "
                    + "from x to y and from y to z are the same singleton, then x and z agree "
                    + "at every bit. The shared bit changes twice and every other bit changes "
                    + "zero times."))),
            DescribeRole.Theorem))));
}
