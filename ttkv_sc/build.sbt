lazy val root = (project in file("."))
  .settings(
    name := "ttkv",
    libraryDependencies ++= Seq(
      "org.typelevel" %% "cats-effect" % "3.5.4",
      "org.typelevel" %% "alleycats-core" % "2.10.0",
      "org.scalacheck" %% "scalacheck" % "1.15.4" % "test"
    ),
    scalacOptions ++= Seq(
      "-feature",
      "-deprecation",
      "-unchecked",
      "-language:higherKinds",
      "-Ypartial-unification"
    )
  )
