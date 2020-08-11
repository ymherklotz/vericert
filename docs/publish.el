;; Publishing projects, this one is for the zettelkasten
(setq org-publish-project-alist
      '(("orgfiles"
         :base-directory "./"
         :base-extension "org"
         :publishing-directory "./html/"
         :publishing-function org-html-publish-to-html)
        ("assets"
         :base-directory "./css/"
         :base-extension "css"
         :publishing-directory "./html/css/"
         :publishing-function org-publish-attachment)
        ("documentation" :components ("orgfiles" "assets"))))
