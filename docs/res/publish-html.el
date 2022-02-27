(require 'package)
(package-initialize)

(require 'org)
(require 'org-transclusion)
(require 'ox)
(require 'ox-html)

(setq org-transclusion-exclude-elements nil)

(org-transclusion-add-all)
(org-html-export-to-html)
