using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PointwiseRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pointwise registration programs over finite object states.",
        H("PointwiseRegistrationTemplates"),
        Blocks(
            Node("pointwiseEqSignature", "Two typed CUT readouts retain the two terms of a pointwise equation.", DescribeRole.Definition),
            Node("pointwiseEqRealization", "The two supplied functions remain the readouts, with no theorem-based reduction.", DescribeRole.Definition),
            Node("pointwiseEqArena", "The law equates the two readouts at every state of the supplied finite arena.", DescribeRole.Definition),
            Node("pointwiseEqLegacy", "The complete universally quantified equation is definitionally the generated law.", DescribeRole.Theorem),
            Node("pointwiseEq_sensitivity", "Two distinct output values and an inhabited arena witness sensitivity of each individual CUT slot.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
