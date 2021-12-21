import scala.annotation.tailrec
import scala.math.{exp, pow}

object valueComputer extends App {
  val AvgLatency: BigDecimal = 0.9
  val VoterMiningRate: BigDecimal = 0.1
  val Beta: BigDecimal = 0.2
  val NetworkDelta: BigDecimal = 3.0
  val VoterChains: Int = 100
  val LogEpsilon: BigDecimal = 20.0
  val DeConfirmHeadroom: BigDecimal = 1.05
  val LogEpsilonConfirm: BigDecimal = LogEpsilon * DeConfirmHeadroom // Confidence level for confirmation = 10^-(val)
  val LogEpsilonDeConfirm: BigDecimal = LogEpsilon // Confidence level for de-confirmation = 10^-(val)
  lazy val CalculateSmallDeltaDeConfirm: BigDecimal =
    solveSmallDelta(
      VoterMiningRate * (1.0 - Beta),
      VoterMiningRate * Beta,
      NetworkDelta,
      BigDecimal(exp(-LogEpsilonDeConfirm.toDouble)),
      VoterChains,
      AvgLatency
    )
  lazy val CalculateSmallDeltaConfirm: BigDecimal =
    solveSmallDelta(
      VoterMiningRate * (1.0 - Beta),
      VoterMiningRate * Beta,
      NetworkDelta,
      BigDecimal(exp(-LogEpsilonConfirm.toDouble)),
      VoterChains,
      AvgLatency
    )

  for (le <- 5 to 23) {
    println(s"Calculating for LogEpsilon = $le")
    val LogEpsilonConfirm: BigDecimal = le * DeConfirmHeadroom
    val LogEpsilonDeConfirm: BigDecimal = le
    val smallDeltaConfirm = solveSmallDelta(
      VoterMiningRate * (1.0 - Beta),
      VoterMiningRate * Beta,
      NetworkDelta,
      BigDecimal(exp(-LogEpsilonConfirm.toDouble)),
      VoterChains,
      AvgLatency
    )
    val smallDeltaDeConfirm = solveSmallDelta(
      VoterMiningRate * (1.0 - Beta),
      VoterMiningRate * Beta,
      NetworkDelta,
      BigDecimal(exp(-LogEpsilonDeConfirm.toDouble)),
      VoterChains,
      AvgLatency
    )
    println(s"For LogEpsilon = $le - SDC = $smallDeltaConfirm and SDDC = $smallDeltaDeConfirm")
  }

//  val SmallDeltaDeConfirm = prismConfig.smallDeltaDeConfirm
//  val SmallDeltaConfirm = prismConfig.smallDeltaConfirm

  /**
   * Checks if the effective vote for the proposer block is greater than a threshold; if it is, the proposer block is
   * confirmed in accordance to the rule defined in Theorem 1 of the paper.
   * Prism Made Practical: Scaling Bitcoin by 10,000x TODO: Link to the paper
   * @param depthSum Sum of depth of all the votes that voted for said proposer block
   * @param nonVote number of votes that voted against the proposer block
   * @param confirmBool Boolean argument where "true" implies we are filtering the proposer block for confirmation
   * (thus implying higher confidence set by logEpsilonConfirm) and "false" implies we are filtering the proposer
   * block to deconfirm existing leader at that level (thus implying lower confidence set by logEpsilonDeConfirm)
   * @return Boolean denoting whether the proposer block with the given vote profile is confirmed or not.
   *         True = Confirmed. The function is designed to make sure that only one proposer block at a level is
   *         confirmed for all possible vote profiles; this is ensured by having threshold: th > 0.5
   */
//  def tryConfirm(depthSum: BigInt, nonVote: Int, confirmBool: Boolean): Boolean = {
//    val lhP = lhPrime(VoterMiningRate * (1.0 - Beta), NetworkDelta)
//    val SmallDelta = if (confirmBool) SmallDeltaConfirm else SmallDeltaDeConfirm
//    //    val SmallDelta = SmallDeltaDeConfirm
//    val t: BigDecimal = BigDecimal(depthSum) / ((1.0 + SmallDelta) * VoterChains * VoterMiningRate)
//    val th = nonVote / VoterChains + 0.5 + SmallDelta
//    val hDelta = 1.0 - functionQ(t, lhP, VoterMiningRate * Beta)
//    // hDelta is the effective vote for the proposer block at level l considering a worst case attack
//    hDelta >= th
//  }

  /** FunctionQ calculates the approximate success probability of a worst case attack to reverse a voter block
   * These definitions can be found through Theorem 1 of the Prism Made Practical: Scaling Bitcoin by 10,000x paper.
   * @param t normalized sum of the depth of votes
   * @param lh honest mining rate adjusted according to network delay
   * @param la adversarial mining rate
   * @return Q
   */
  def functionQ(t: BigDecimal, lh: BigDecimal, la: BigDecimal): BigDecimal = {
    val terms: Int = 40
    // In the paper Prism Made Practical: Scaling Bitcoin by 10,000x; the function q involves an infinite summation;
    // we approximate it with a summation of the first 40 terms and ignore the rest

    var res: BigDecimal = 1.0

    for (l <- 0 to terms) {
      val term1: BigDecimal = (lh - la) / lh * BigDecimal(pow(la.toDouble / lh.toDouble, l))
      var term2: BigDecimal = 0.0
      for (k <- l to terms) {
        val term2V1: BigDecimal = BigDecimal(exp(-lh.toDouble * t.toDouble)) * factdiv(lh * t, k)
        var term2V2: BigDecimal = 0.0
        for (n <- 0 to k - l) {
          val term2V2V1
          : BigDecimal = BigDecimal(exp(-la.toDouble * t.toDouble)) * factdiv(la * t, n) * (1.0 - BigDecimal(
            pow(la.toDouble / lh.toDouble, (k - n - l).toInt)
          ))
          term2V2 = term2V2 + term2V2V1
        }
        term2 = term2 + term2V1 * term2V2
      }
      res = res - term1 * term2
    }
    res
  }

  /**
   * Honest chain growth accounting for network delay
   * @param lh Honest mining rate
   * @param delta Network delay
   * @return Honest chain growth poisson rate
   */
  def lhPrime(lh: BigDecimal, delta: BigDecimal): BigDecimal = {
    lh / (1.0 + lh * delta)
  }

  def solveTDelta(
                   lh: BigDecimal,
                   la: BigDecimal,
                   delta: BigDecimal,
                   smallDelta: BigDecimal,
                   avgLatency: BigDecimal
                 ): BigDecimal = {
    val lhP = {
      lhPrime(lh, delta)
    }
    val th = 0.5 + smallDelta
    @tailrec
    def loop(res: BigDecimal): BigDecimal = {
      val hDelta: BigDecimal = 1.0 - functionQ(res, lhP, la)
      val d = (hDelta - th).abs
      if (d < 0.01) {
        res
      } else {
        loop(res + 1.0)
      }
    }
    loop(1.0)
  }

  def solveSmallDelta(
                       lh: BigDecimal,
                       la: BigDecimal,
                       delta: BigDecimal,
                       ep: BigDecimal,
                       m: Int,
                       avgLatency: BigDecimal
                     ): BigDecimal = {
    @tailrec
    def loop(tmpRes: BigDecimal, tDelta: BigDecimal): BigDecimal = {
      val ourEp = errorProb(lh + la, m, tmpRes, tDelta)
      if (ourEp > ep) {
        loop(tmpRes + 0.001, tDelta)
      } else {
        tmpRes
      }
    }
    @tailrec
    def externalLoop(res: BigDecimal, counter: Int): BigDecimal = {
      if (counter == 0) {
        res
      } else {
        val tDelta = solveTDelta(lh, la, delta, res, avgLatency)
        externalLoop(loop(res, tDelta), counter - 1)
      }
    }
    val res = externalLoop(0.0, 5)
    res
  }

  def errorProb(l: BigDecimal, m: Int, smallDelta: BigDecimal, tDelta: BigDecimal): BigDecimal = {
    /* BigDecimal does not support Exp. Confirmation functions do not need to be very precise/reproducible.
    A loss of reproducibility is fine since different machines will eventually confirm the same blocks; we don't use
    confidence directly to make on-chain decisions.
    We can convert all BigDecimal to Double (if needed for performance requirements) with little effect on security.
     */
    BigDecimal(
      exp((-2.0 * smallDelta * smallDelta * m).toDouble) + 2.0 * exp(
        (
          -(smallDelta * smallDelta * tDelta *
            l * m) / 3.0
          ).toDouble
      )
    )
  }

  def factdiv(up: BigDecimal, n: Int): BigDecimal = {
    var res: BigDecimal = 1.0
    for (i <- 1 to n) {
      res = res * up / i
    }
    res
  }
}