using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class CapacityBoxOneBitRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unit-edge embeddings of capacity boxes assign the same colour to opposite edges of each coordinate square.",
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
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("unit-edge"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.UnitEdge"),
            H("Directed capacity edge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A unit edge increases one capacity coordinate by one while fixing every other coordinate."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("one-bit-embedding"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.OneBitEmbedding"),
            H("One-bit capacity code"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "A one-bit capacity code is injective and maps every unit edge to two Boolean words at Hamming distance one."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("raise"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.raise"),
            H("Increase one coordinate"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The indicated coordinate is increased by one when its value is below capacity."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("unit-edge-colour"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.unitEdgeColour"),
            H("Colour of a capacity edge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The colour of a capacity edge is the unique bit changed by its image."))),
            DescribeRole.Definition),
        Describe.Lean(
            DescribeId.Create("layer-colour-invariant"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Coding/CapacityBoxOneBitRigidity.layer_colour_invariant"),
            H("Transport across a coordinate square"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Increasing a different coordinate leaves the colour of a fixed layer edge unchanged. Injectivity keeps both diagonals of the image square nondegenerate."))),
            DescribeRole.Theorem))));
}
