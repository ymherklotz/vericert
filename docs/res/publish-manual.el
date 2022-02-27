(require 'package)
(package-initialize)

(require 'org)
(require 'org-transclusion)
(require 'ox)
(require 'ox-texinfo)

(setq org-transclusion-exclude-elements nil)

(org-transclusion-add-all)
(org-texinfo-export-to-texinfo)
