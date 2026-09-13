using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class CapacityBoxOneBitRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Boolean hypercube cannot return to a different diagonal after two consecutive edges use the same bit.",
        H("Capacity Box One-Bit Rigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("edge-colour"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.edgeColour"),
            H("Colour of a unit Boolean edge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The colour of a unit edge is the unique coordinate at which its two Boolean "
                    + "words differ."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("square-opposite-edges-same-colour"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.square_opposite_edges_same_colour"),
            H("Opposite edges of a Boolean square have the same colour"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "In a nondegenerate four-cycle of Boolean words whose edges each change one "
                    + "coordinate, the two opposite edges change the same coordinate."))),
            DescribeRole.Theorem),
        Describe.Lean(
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
