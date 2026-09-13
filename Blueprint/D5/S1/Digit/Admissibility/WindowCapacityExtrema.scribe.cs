using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class WindowCapacityExtremaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extremal Fibonacci Window Widths.",
        H("Extremal Fibonacci Window Widths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("windowcapacityextrema-maximizer-has-extremal-shape"),
                DeclarationHandle.Create("D5/S1/Digit/Admissibility/WindowCapacityExtrema.maximizer_has_extremal_shape"),
                H("Necessary shapes of a maximizing width vector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a positive number of registers and a nonnegative total width. "
                    + "If a width vector maximizes the product of Fibonacci window sizes among all "
                    + "vectors with that total width, then at or below the register count every width "
                    + "is zero or one. At or above the register count, every width except one is one, "
                    + "and the remaining width is the total minus the register count plus one. "
                    + "At equality of total width and register count both descriptions give all ones. "
                    + "Moving width from a coordinate of size at least two to a zero coordinate "
                    + "strictly increases the product, as does combining two widths of size at least "
                    + "two into their sum minus one and a width of one."))),
                DescribeRole.Theorem))));
}
