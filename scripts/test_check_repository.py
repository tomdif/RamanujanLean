"""Regression tests for the Markdown navigation checker."""
import unittest

from check_repository import markdown_anchors, markdown_prose


class MarkdownNavigationTests(unittest.TestCase):
    def test_inline_formatting_and_unicode(self):
        self.assertEqual(markdown_anchors("## `τ(n)` & *Γ* — [proof](proof.md)\n"),
                         {"τn--γ--proof"})

    def test_duplicate_and_colliding_headings(self):
        self.assertEqual(markdown_anchors("# A\n# A\n# A-1\n# A\n"),
                         {"a", "a-1", "a-1-1", "a-2"})

    def test_fences_do_not_create_anchors_or_links(self):
        source = "```md\n# hidden\n[x](missing.md)\n```\n# Visible\n"
        self.assertEqual(markdown_anchors(source), {"visible"})
        self.assertNotIn("missing.md", markdown_prose(source))

    def test_tilde_fences_and_longer_closing_fences(self):
        self.assertEqual(markdown_anchors("~~~\n# hidden\n~~~~\n## shown\n"), {"shown"})

    def test_html_anchors_and_entities(self):
        self.assertEqual(markdown_anchors('<a id="explicit"></a>\n## A &amp; B\n'),
                         {"explicit", "a--b"})

    def test_closing_hashes_and_missing_target(self):
        anchors = markdown_anchors("## Real heading ##\n")
        self.assertIn("real-heading", anchors)
        self.assertNotIn("old-heading", anchors)


if __name__ == "__main__":
    unittest.main()
