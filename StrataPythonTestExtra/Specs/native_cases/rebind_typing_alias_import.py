# One import statement that binds the typing alias to another module too rejects the model.
import typing as t, import_test.service.module as t
