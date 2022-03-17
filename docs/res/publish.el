(require 'package)
(package-initialize)

(require 'org)
(require 'org-transclusion)
(require 'ox)
(require 'ox-html)
(require 'htmlize)
(require 'ox-texinfo)
(require 'ox-man)

(setq org-transclusion-exclude-elements nil
      org-html-head-include-default-style nil
      org-html-head-include-scripts nil
      org-html-postamble-format '(("en" ""))
      org-html-postamble t
      org-html-divs '((preamble "header" "header")
                      (content "article" "content")
                      (postamble "footer" "postamble"))
      org-html-doctype "html5"
      org-html-htmlize-output-type 'css)

(org-transclusion-add-all)
