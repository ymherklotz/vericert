(require 'package)
(package-initialize)

(require 'org)
(require 'org-transclusion)
(require 'ox)
(require 'ox-man)

(setq org-transclusion-exclude-elements nil)

(org-transclusion-add-all)
(org-man-export-to-man)
